module Agda.Compiler.ToForth where

import Prelude hiding ( null , empty )

import Agda.Compiler.Common
import Agda.Compiler.ToTreeless
import Agda.Compiler.Treeless.EliminateLiteralPatterns

import Agda.Syntax.Abstract.Name
import Agda.Syntax.Common
import Agda.Syntax.Internal ( conName )
import Agda.Syntax.Literal
import Agda.Syntax.Treeless

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty

import Agda.Utils.Impossible
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Pretty
import Agda.Utils.Singleton

import Control.DeepSeq ( NFData )

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State

import Data.Char
import Data.SCargot.Repr
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T

import GHC.Generics ( Generic )

type SchAtom = Text
type SchForm = RichSExpr SchAtom

makepretty :: Bool
makepretty = True

newLine :: String
newLine
  | makepretty = "\n"
  | otherwise = ""

formToAtom :: SchForm -> SchAtom
formToAtom (RSAtom ret) = T.append ret (T.pack " ")
formToAtom (RSList xs) = T.concat (map formToAtom xs)
formToAtom (RSDotted xs y) = T.append (T.concat (map formToAtom xs)) y
-- formToAtom (RSAtom ret) = T.append ret (T.pack " ")
-- formToAtom (RSList xs) = T.concat [ T.pack "L( ", T.concat (map formToAtom xs), T.pack " )L "]
-- formToAtom (RSDotted xs y) = T.concat [ T.pack "D( ", T.append (T.concat (map formToAtom xs)) y, T.pack " )D "]

schDefine :: SchAtom -> SchForm -> SchForm
schDefine f body = RSList
  ["define", RSList [RSAtom f], body]

fthWord :: SchAtom -> SchForm -> SchForm
fthWord f body = RSAtom (
  T.pack ("defer " ++ T.unpack f ++ "\nvariable XT"++ T.unpack f ++"\n:noname "++ " " ++ T.unpack (formToAtom body) ++
  " ; XT" ++ T.unpack f ++ " !\n:noname" ++ " XT" ++ T.unpack f ++ " @ makeTHUNK ; is " ++ T.unpack f))
  where
    replaceF :: SchAtom -> SchForm -> SchForm
    replaceF f (RSAtom word)
      | word == f = RSAtom "recurse"
      | otherwise = RSAtom $ T.replace (T.concat [T.pack " ", f, T.pack " "]) (T.pack " recurse ") word
    replaceF f (RSList xs) = RSList $ map (replaceF f) xs
    replaceF f (RSDotted xs y) = RSDotted (map (replaceF f) xs) (if f == y then T.pack "recurse" else y)


fthDefineType :: SchAtom -> Int -> SchAtom -> SchForm
fthDefineType f args body = RSAtom
  (T.concat [T.pack "variable type", f,
  T.pack " 1 cells allot ", T.pack $ show (args + 1), T.pack " type", f, T.pack " !\n", body, "\n", fthPrinter f ," type", f, " 1 cells + !"])

fthPrinter :: SchAtom -> SchAtom
fthPrinter f = T.concat [
  ":noname .\" ",
  f,
  " \" ;"
  ]

fthConstructor :: SchAtom -> Int -> SchAtom
fthConstructor f args = formToAtom $ fthWord f (RSAtom $ T.pack
    (" type" ++ T.unpack f ++  " here "
    ++ show (args + 1) ++ " fillArray here " ++ show (args + 1) ++ " cells allot"))

-- >>> :t T.pack "variable"
-- T.pack "variable" :: Text

schError :: Text -> SchForm
schError msg = RSList
  [ "begin"
  , RSList ["display", RSAtom ("\"" <> msg <> "\\n\"")]
  , RSList ["exit", "1"]
  ]

schAxiom :: SchAtom -> SchForm
schAxiom f = fthWord f $ schError $ "encountered axiom: " <> f

schLambda :: [SchAtom] -> SchForm -> SchForm
schLambda args body = RSList
  [ RSAtom "lambda"
  , RSList $ map RSAtom args
  , body
  ]


fthLocal :: [SchAtom] -> SchForm -> SchForm
fthLocal args body = RSAtom $ T.pack $
  "{ " ++ concatMap (\arg -> T.unpack arg ++ " ") args ++ "} " ++ newLine ++ T.unpack (formToAtom body)

-- Bind each argument individually instead of all at once.
schLambdas :: [SchAtom] -> SchForm -> SchForm
schLambdas args body = foldr (schLambda . singleton) body args

fthLocals :: [SchAtom] -> SchForm -> SchForm
fthLocals args body = foldr (fthLocal . singleton) body args

schApp :: SchForm -> [SchForm] -> SchForm
schApp f vs = RSList (vs ++ [f])

fthApp :: SchForm -> [SchForm] -> SchForm
fthApp f args = RSList (args ++ [f, " pass "])

-- Apply to each argument individually instead of all at once.
schApps :: SchForm -> [SchForm] -> SchForm
schApps = foldl (\x y -> schApp x [y])

fthApps :: SchForm -> [SchForm] -> SchForm
fthApps = foldl (\x y -> fthApp x [y])

fthLet :: [(SchAtom,SchForm)] -> SchForm -> SchForm
fthLet binds body = RSAtom $ T.pack $
  concatMap (\(x,v) -> T.unpack (formToAtom v) ++ "{ " ++ T.unpack x ++ " " ++ "} ") binds
  ++ T.unpack (formToAtom body)

schLet :: [(SchAtom,SchForm)] -> SchForm -> SchForm
schLet binds body = RSList
  [ RSAtom "let"
  , RSList $ map (\(x,v) -> RSList [RSAtom x,v]) binds
  , body
  ]

schConName :: QName -> SchAtom
schConName x = T.pack $ prettyShow $ qnameName x

schConAtom :: QName -> SchAtom
schConAtom x = T.singleton '\'' <> schConName x

schConApp :: QName -> [SchForm] -> SchForm
schConApp c vs = RSList $
  [ RSAtom "'"
  , RSAtom (schConAtom c)
  ] ++ vs

schCase :: SchForm -> [SchForm] -> Maybe SchForm -> SchForm
schCase x cases maybeFallback = RSList $
  [ RSAtom "record-case"
  , x
  ] ++ cases ++
  [ RSList [ RSAtom "else" , fallback ] | fallback <- maybeToList maybeFallback
  ]

fthPatternMatch :: SchForm -> [SchForm] -> Maybe SchForm -> SchForm
fthPatternMatch x cases maybeFallback  = RSList
  [RSAtom (makeForthy x cases maybeFallback)]
  -- ++
  -- [ RSList [ RSAtom "FALLBACK(?)" , fallback ] | fallback <- maybeToList maybeFallback
  -- ]
    where
      makeForthy :: SchForm -> [SchForm] -> Maybe SchForm -> SchAtom
      makeForthy arg (RSList [pat, RSList wildcards, expr]:xs) fallback = T.concat [
        T.concat [
          formToAtom arg,
          T.concat (map (\x -> T.pack "makeWILDCARD ") wildcards ++ [formToAtom pat] ++ map (\x -> T.pack "pass ") wildcards),
          T.pack "0 pointer !",
          T.concat (T.pack (" obj= if wildcards " ++ show (length wildcards) ++ " pushArray { ") : map formToAtom wildcards ++ [T.pack "} "] ++ [T.pack newLine]),
          formToAtom expr
        ],
        T.pack " else ",
        makeForthy arg xs fallback,
        T.pack " then "
        ]
      makeForthy arg (other:xs) fallback = T.append
        (T.pack "UH OH!, ENCOUNTERED SOMETHING OTHER THAN AN RSLIST WHEN COMPILING PATTERN MATCHING")
        (makeForthy arg xs fallback)
      makeForthy arg [] fallback = T.concat (map formToAtom (maybeToList fallback))


schUnit :: SchForm
schUnit = RSList [RSAtom "list"]

fthUnit :: SchForm
fthUnit = RSList [RSAtom "0"]

schDelay :: SchForm -> SchForm
schDelay x
  | RSList [RSAtom "force", y] <- x = y
  | otherwise                       = RSList [RSAtom "delay", x]

fthDelay :: SchForm -> SchForm
fthDelay x
  | RSList [y, RSAtom "dethunk"] <- x = y
  | otherwise                       = RSList [x, RSAtom "makeTHUNK"]

schForce :: SchForm -> SchForm
schForce x
  | RSList [RSAtom "delay", y] <- x = y
  | otherwise                       = RSList [RSAtom "force", x]

fthForce :: SchForm -> SchForm
fthForce x = RSList [x, RSAtom "dethunk"]


fthAdd, fthSub, fthMul, fthQuot, fthRem, fthIf, fthEq, fthGeq, fthLt :: SchForm
fthAdd  = RSList [RSAtom "add"]
fthSub  = RSList [RSAtom "sub"]
fthMul  = RSList [RSAtom "mul"]
fthQuot = RSList [RSAtom "quot"]
fthRem  = RSList [RSAtom "rem"]
fthIf   = RSList [RSAtom "iff"]
fthEq   = RSList [RSAtom "eq"]
fthGeq   = RSList [RSAtom "geq"]
fthLt   = RSList [RSAtom "lt"]

fthPreamble :: ToSchemeM [SchForm]
fthPreamble = do
  force <- makeForce
  return
    [ fthWord "add"  $ fthLocals ["m","n"] $ RSAtom $ formToAtom $ RSList [force (RSAtom "m dethunk"), force (RSAtom "n dethunk"), RSAtom "+"]
    , fthWord "sub"  $ fthLocals ["m","n"] $ RSAtom $ formToAtom $ RSList [force (RSAtom "m dethunk"), force (RSAtom "n dethunk"), RSAtom "-"]
    , fthWord "mul"  $ fthLocals ["m","n"] $ RSAtom $ formToAtom $ RSList [force (RSAtom "m dethunk"), force (RSAtom "n dethunk"), RSAtom "*"]
    , fthWord "quot" $ fthLocals ["m","n"] $ RSAtom $ formToAtom $ RSList [force (RSAtom "m dethunk"), force (RSAtom "n dethunk"), RSAtom "/"]
    , fthWord "rem"  $ fthLocals ["m","n"] $ RSAtom $ formToAtom $ RSList [force (RSAtom "m dethunk"), force (RSAtom "n dethunk"), RSAtom "mod"]
    , fthWord "iff"  $ fthLocals ["b","x","y"] $ RSAtom $ formToAtom $ RSList [force (RSAtom "b dethunk"), RSAtom "if", force (RSAtom "x dethunk"), RSAtom "else", force (RSAtom "y dethunk"), RSAtom "then"]
    , fthWord "eq"   $ fthLocals ["x","y"] $ RSAtom $ formToAtom $ RSList [force (RSAtom "x dethunk"), force (RSAtom "y dethunk"), RSAtom ""]
    , fthWord "geq"   $ fthLocals ["x","y"] $ RSAtom $ formToAtom $ RSList [force (RSAtom "x dethunk"), force (RSAtom "y dethunk"), RSAtom ">="]
    , fthWord "lt"   $ fthLocals ["x","y"] $ RSAtom $ formToAtom $ RSList [force (RSAtom "x dethunk"), force (RSAtom "y dethunk"), RSAtom "<"]
    
    ]

deriving instance Generic EvaluationStrategy
deriving instance NFData  EvaluationStrategy

data SchOptions = SchOptions
  { schEvaluation :: EvaluationStrategy
  }
  deriving (Generic, NFData)

data ToSchemeEnv = ToSchemeEnv
  { toSchemeOptions :: SchOptions
  , toSchemeVars    :: [SchAtom]
  }

initToSchemeEnv :: SchOptions -> ToSchemeEnv
initToSchemeEnv opts = ToSchemeEnv opts []

addVarBinding :: SchAtom -> ToSchemeEnv -> ToSchemeEnv
addVarBinding x env = env { toSchemeVars = x : toSchemeVars env }

data ToSchemeState = ToSchemeState
  { toSchemeFresh     :: [SchAtom]          -- Used for locally bound named variables
  , toSchemeDefs      :: Map QName SchAtom  -- Used for global definitions
  , toSchemeUsedNames :: Set SchAtom        -- Names that are already in use (both variables and definitions)
  }

-- This is an infinite supply of variable names
-- a, b, c, ..., z, a1, b1, ..., z1, a2, b2, ...
-- We never reuse variable names to make the code easier to
-- understand.
freshVars :: [SchAtom]
freshVars = concat [ map (<> i) xs | i <- "":map (T.pack . show) [1..] ]
  where
    xs = map T.singleton ['a'..'z']

-- These are names that should not be used by the code we generate
reservedNames :: Set SchAtom
reservedNames = Set.fromList $ map T.pack
  [ "loop"
  -- TODO: add more
  ]

initToSchemeState :: ToSchemeState
initToSchemeState = ToSchemeState
  { toSchemeFresh     = freshVars
  , toSchemeDefs      = Map.empty
  , toSchemeUsedNames = reservedNames
  }

type ToSchemeM a = StateT ToSchemeState (ReaderT ToSchemeEnv TCM) a

runToSchemeM :: SchOptions -> ToSchemeM a -> TCM a
runToSchemeM opts =
    (`runReaderT` initToSchemeEnv opts)
  . (`evalStateT` initToSchemeState)


freshSchAtom :: ToSchemeM SchAtom
freshSchAtom = do
  names <- gets toSchemeFresh
  case names of
    [] -> fail "No more variables!"
    (x:names') -> do
      modify $ \st -> st { toSchemeFresh = names' }
      ifM (isNameUsed x) freshSchAtom $ {-otherwise-} do
        setNameUsed x
        return x

getEvaluationStrategy :: ToSchemeM EvaluationStrategy
getEvaluationStrategy = reader $ schEvaluation . toSchemeOptions

makeDelay :: ToSchemeM (SchForm -> SchForm)
makeDelay = return id
  -- do
  -- strat <- getEvaluationStrategy
  -- case strat of
  --   EagerEvaluation -> return id
  --   LazyEvaluation  -> return fthDelay

makeForce :: ToSchemeM (SchForm -> SchForm)
makeForce = return id
  -- do
  -- strat <- getEvaluationStrategy
  -- case strat of
  --   EagerEvaluation -> return id
  --   LazyEvaluation  -> return fthForce

getVarName :: Int -> ToSchemeM SchAtom
getVarName i = reader $ (!! i) . toSchemeVars

withFreshVar :: (SchAtom -> ToSchemeM a) -> ToSchemeM a
withFreshVar f = do
  x <- freshSchAtom
  local (addVarBinding x) $ f x

withFreshVars :: Int -> ([SchAtom] -> ToSchemeM a) -> ToSchemeM a
withFreshVars i f
  | i <= 0    = f []
  | otherwise = withFreshVar $ \x -> withFreshVars (i-1) (f . (x:))

saveDefName :: QName -> SchAtom -> ToSchemeM ()
saveDefName n a = modify $ \s -> s { toSchemeDefs = Map.insert n a (toSchemeDefs s) }

isNameUsed :: SchAtom -> ToSchemeM Bool
isNameUsed x = gets (Set.member x . toSchemeUsedNames)

setNameUsed :: SchAtom -> ToSchemeM ()
setNameUsed x = modify $ \s ->
  s { toSchemeUsedNames = Set.insert x (toSchemeUsedNames s) }

-- Extended alphabetic characters that are allowed to appear in
-- a Scheme identifier
schemeExtendedAlphaChars :: Set Char
schemeExtendedAlphaChars = Set.fromList
  [ '!' , '$' , '%' , '&' , '*' , '+' , '-' , '.' , '/' , ':' , '<' , '=' , '>'
  , '?' , '@' , '^' , '_' , '~'
  ]

-- Categories of unicode characters that are allowed to appear in
-- a Scheme identifier
schemeAllowedUnicodeCats :: Set GeneralCategory
schemeAllowedUnicodeCats = Set.fromList
  [ UppercaseLetter , LowercaseLetter , TitlecaseLetter , ModifierLetter
  , OtherLetter , NonSpacingMark , SpacingCombiningMark , EnclosingMark
  , DecimalNumber , LetterNumber , OtherNumber , ConnectorPunctuation
  , DashPunctuation , OtherPunctuation , CurrencySymbol , MathSymbol
  , ModifierSymbol , OtherSymbol , PrivateUse
  ]

-- True if the character is allowed to be used in a Scheme identifier
isValidSchemeChar :: Char -> Bool
isValidSchemeChar x
  | isAscii x = isAlphaNum x || x `Set.member` schemeExtendedAlphaChars
  | otherwise = generalCategory x `Set.member` schemeAllowedUnicodeCats

-- Creates a valid Scheme name from a (qualified) Agda name.
-- Precondition: the given name is not already in toSchemeDefs.
makeSchemeName :: QName -> ToSchemeM SchAtom
makeSchemeName n = do
  a <- go $ fixName $ prettyShow $ qnameName n
  saveDefName n a
  setNameUsed a
  return a
  where
    nextName = ('z':) -- TODO: do something smarter

    go s     = ifM (isNameUsed $ T.pack s) (go $ nextName s) (return $ T.pack s)

    fixName s =
      let s' = concatMap fixChar s in
      if isNumber (head s') then "z" ++ s' else s'

    fixChar c
      | isValidSchemeChar c = [c]
      | otherwise           = "\\x" ++ toHex (ord c) ++ ";"

    toHex 0 = ""
    toHex i = toHex (i `div` 16) ++ [fourBitsToChar (i `mod` 16)]

fourBitsToChar :: Int -> Char
fourBitsToChar i = "0123456789ABCDEF" !! i
{-# INLINE fourBitsToChar #-}

class ToScheme a b where
  toScheme :: a -> ToSchemeM b

instance ToScheme QName SchAtom where
  toScheme n = do
    r <- gets (Map.lookup n . toSchemeDefs)
    case r of
      Nothing -> makeSchemeName n
      Just a  -> return a

instance ToScheme Definition (Maybe SchForm) where
  toScheme def
    | defNoCompilation def ||
      not (usableModality $ getModality def) = return Nothing
  toScheme def = do
    let f = defName def
    case theDef def of
      Axiom{} -> do
        return $ Just $ RSAtom ""
      GeneralizableVar{} -> return Nothing
      d@Function{} | d ^. funInline -> return Nothing
      Function{} -> do
        f' <- toScheme f
        strat <- getEvaluationStrategy
        maybeCompiled <- liftTCM $ toTreeless strat f
        case maybeCompiled of
          Just body -> Just . fthWord f' <$> toScheme body
          Nothing   -> return Nothing
      Primitive{} -> do
        f' <- toScheme f
        return $ Just $ schAxiom f' -- TODO!
      PrimitiveSort{} -> return Nothing
      Datatype{} -> return Nothing
      Record{} -> return Nothing
      Constructor{ conSrcCon = chead, conArity = nargs } -> do
        let c = conName chead
        c' <- toScheme c
        withFreshVars nargs $ \xs ->
          return $ Just $ fthDefineType c' (length xs) (fthConstructor c' (length xs))

      AbstractDefn{} -> __IMPOSSIBLE__
      DataOrRecSig{} -> __IMPOSSIBLE__


instance ToScheme TTerm SchForm where
  toScheme v = do
    v <- liftTCM $ eliminateLiteralPatterns v
    case v of
      TVar i -> do
          name <- getVarName i
          force <- makeForce
          return $ force $ RSAtom name
      TPrim p -> toScheme p
      TDef d -> do
        d' <- toScheme d
        return $ RSList [RSAtom d']
      TApp f args -> do
        f' <- toScheme f
        delay <- makeDelay
        args' <- map delay <$> traverse toScheme args
        return $ fthApps f' args'
      TLam v -> withFreshVar $ \x -> do
        body <- toScheme v
        return $ fthLocal [x] body
      TLit l -> toScheme l
      TCon c -> do
        c' <- toScheme c
        return $ RSList [RSAtom c']
      TLet u v -> do
        expr <- toScheme u
        withFreshVar $ \x -> do
          body <- toScheme v
          return $ fthLet [(x,expr)] body
      TCase i info v bs -> do
        force <- makeForce
        x <- force . RSAtom <$> getVarName i
        cases <- traverse toScheme bs
        fallback <- if isUnreachable v
                    then return Nothing
                    else Just <$> toScheme v
        return $ fthPatternMatch x cases fallback
      TUnit -> return fthUnit
      TSort -> return fthUnit
      TErased -> return fthUnit
      TCoerce u -> toScheme u
      TError err -> toScheme err

    where
      isUnreachable v = v == TError TUnreachable

instance ToScheme TPrim SchForm where
  toScheme p = case p of
    PAdd  -> return fthAdd
    PSub  -> return fthSub
    PMul  -> return fthMul
    PQuot -> return fthQuot
    PRem  -> return fthRem
    PIf   -> return fthIf
    PEqI  -> return fthEq
    _     -> return $ schError $ T.pack $ "not yet supported: primitive " ++ show p

instance ToScheme Literal SchForm where
  toScheme lit = case lit of
    LitNat    x -> return $ RSAtom (T.pack (show x))
    LitWord64 x -> return $ schError "not yet supported: Word64 literals"
    LitFloat  x -> return $ schError "not yet supported: Float literals"
    LitString x -> return $ schError "not yet supported: String literals"
    LitChar   x -> return $ schError "not yet supported: Char literals"
    LitQName  x -> return $ schError "not yet supported: QName literals"
    LitMeta p x -> return $ schError "not yet supported: Meta literals"


-- TODO: allow literal branches and guard branches
instance ToScheme TAlt SchForm where
  toScheme alt = case alt of
    TACon c nargs v -> withFreshVars nargs $ \xs -> do
      body <- toScheme v
      return $ RSList [RSList [RSAtom (schConName c)], RSList (map RSAtom xs), body]

    TAGuard{} -> __IMPOSSIBLE__ -- TODO
    TALit{}   -> __IMPOSSIBLE__ -- TODO

instance ToScheme TError SchForm where
  toScheme err = case err of
    TUnreachable -> return $ schError "Panic!"
    TMeta s      -> return $ schError $ "encountered unsolved meta: " <> T.pack s
