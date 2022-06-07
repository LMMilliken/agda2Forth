module Agda.Compiler.ToForth where

import Prelude hiding ( null , empty )

import Agda.Compiler.Common
import Agda.Compiler.ToTreeless
import Agda.Compiler.Treeless.EliminateLiteralPatterns
import Agda.Compiler.Treeless.GuardsToPrims
import Agda.Syntax.Abstract.Name
import Agda.Syntax.Common
import Agda.Syntax.Internal as I
import Agda.Syntax.Literal
import Agda.Syntax.Treeless

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Primitive.Base
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
import System.IO
import Paths_agda2forth
import Foreign.Marshal.Unsafe (unsafeLocalState)

type FthAtom = Text
type FthForm = RichSExpr FthAtom

makepretty :: Bool
makepretty = True

newLine :: String
newLine
  | makepretty = "\n"
  | otherwise = ""

formToAtom :: FthForm -> FthAtom
formToAtom (RSAtom ret) = T.append ret (T.pack " ")
formToAtom (RSList xs) = T.concat (map formToAtom xs)
formToAtom (RSDotted xs y) = T.append (T.concat (map formToAtom xs)) y

fthWord :: FthAtom -> FthForm -> FthForm
fthWord f body
  | countLambdas body == 0 = fthSimpleWord f body
  | otherwise = RSAtom (
  T.pack ("ENDFLAG \n " ++ T.unpack (formToAtom body) ++
  "create XT"++ T.unpack f ++" fillHere \n "++
  ":noname" ++ " XT" ++ T.unpack f ++ " foldThunks ; is " ++ T.unpack f))

fthSimpleWord :: FthAtom -> FthForm -> FthForm
fthSimpleWord f body = RSAtom (
  T.pack ("variable XT"++ T.unpack f ++"\n:noname "++ " " ++ T.unpack (formToAtom body) ++
  " ; XT" ++ T.unpack f ++ " !\n:noname" ++ " XT" ++ T.unpack f ++ " @ makeTHUNK ; is " ++ T.unpack f))

fthDefineType :: FthAtom -> Int -> FthAtom -> FthForm
fthDefineType f args body = RSAtom
  (T.concat [T.pack "variable type", f,
  T.pack " 1 cells allot ", T.pack $ show (args + 1), T.pack " type", f, T.pack " !\n", body, "\n", fthPrinter f ," type", f, " 1 cells + !"])

fthPrinter :: FthAtom -> FthAtom
fthPrinter f = T.concat [
  ":noname .\" ",
  f,
  " \" ;"
  ]

fthConstructor :: FthAtom -> Int -> FthAtom
fthConstructor f args = formToAtom $ fthSimpleWord f (RSAtom $ T.pack
    (" type" ++ T.unpack f ++  " here "
    ++ show (args + 1) ++ " fillArray here " ++ show (args + 1) ++ " cells allot"))

fthError :: Text -> FthForm
fthError msg = RSAtom $ T.pack ("cr .\" " ++ T.unpack msg ++ " \" bye")

fthAxiom :: FthAtom -> FthForm
fthAxiom f = fthWord f $ fthError $ "encountered axiom: " <> f


fthLocal :: [FthAtom] -> FthForm -> FthForm
fthLocal args body = RSAtom $ T.pack $
  "{ " ++ concatMap (\arg -> T.unpack arg ++ " ") args ++ "} " ++ newLine ++ T.unpack (formToAtom body)


fthLambda :: [FthAtom] -> [FthAtom] -> FthForm -> FthForm
fthLambda args lambdas body = RSAtom $ T.pack $
  "!LAM! :LAM { " ++ bindings ++ "} " ++ newLine ++ replaceLambda lambdas (addArgs $ T.unpack injected) ++ " LAM;"
  where
    replaceLambda (x:xs) ('!':'L':'A':'M':'!':rest) = " !LA " ++ T.unpack x ++ " M! " ++ replaceLambda xs rest
    replaceLambda xs (y:ys) = y:replaceLambda xs ys
    replaceLambda xs [] = []

    addArgs ('!':'L':'A':rest) = T.unpack (T.intercalate " " ( reverse args)) ++ " !LA" ++ addPasses rest
    addArgs (x:xs) = x:addArgs xs
    addArgs [] = []

    addPasses ('M':'!':rest) = "M! " ++ concatMap (const " pass ") args ++ addArgs rest
    addPasses (x:xs) = x:addPasses xs
    addPasses [] = []

    bindings = concatMap (\arg -> T.unpack arg ++ " ") args ++ " ( LAM ) " ++ concatMap (\arg -> T.unpack arg ++ " ") lambdas
    -- bindings = concatMap (\arg -> T.unpack arg ++ " ") (args ++ lambdas)

    injected =
      -- T.replace " } " (T.append " } " (T.append (T.intercalate " " lambdas) " ")) $
      T.replace " ( LAM ) " (T.append (T.append (T.intercalate " " args) " ") " ( LAM ) ") (formToAtom body)


fixWord :: Text -> Text
fixWord word = T.concat [f, " ", T.pack (snd (moveLambdas (T.unpack body) []))]
  where
    (f, body) = T.breakOn "\n" word


moveLambdas :: String -> String -> (String, String)
moveLambdas (':':'L':'A':'M':' ':rest) acc = moveLambdas rest2 (acc2++acc)
  where
    (rest2, acc2) = moveLambdas rest ":noname "
moveLambdas (' ':'L':'A':'M':';':rest) acc = (rest, acc ++ " ; \n")
moveLambdas (x:rest) acc = moveLambdas rest (acc++[x])
moveLambdas [] acc = ([], T.unpack $ replaceOne (removeMany ["!LA", "M!", " ( LAM )"] (T.pack acc)))

removeMany :: [Text] -> Text -> Text
removeMany xs str = foldr (`T.replace` "") str xs


replaceOne :: Text -> Text
replaceOne text
  | T.null back = text
  | otherwise = T.concat [front, "makeTHUNK", T.drop 14 back]
    where
      (front, back) = T.breakOn "makeTHUNK pass" text

countOccurences :: Text -> Text -> Int
countOccurences t s = sum [ 1 | r <- T.tails s, T.isPrefixOf t r ]

countLambdas :: FthForm -> Int
countLambdas (RSAtom atom) = countOccurences "!LAM!" atom
countLambdas x = countLambdas (RSAtom (formToAtom x))


-- >>> countOccurences (T.pack "hi") (T.pack "hihihi")
-- 3

-- Bind each argument individually instead of all at once.
fthLocals :: [FthAtom] -> FthForm -> FthForm
fthLocals args body = foldr (fthLocal . singleton) body args

fthApp :: FthForm -> [FthForm] -> FthForm
fthApp f args = RSList (args ++ [f, " pass "])

-- Apply to each argument individually instead of all at once.
fthApps :: FthForm -> [FthForm] -> FthForm
fthApps = foldl (\x y -> fthApp x [y])

fthLet :: [(FthAtom,FthForm)] -> FthForm -> FthForm
fthLet binds body = RSAtom $ T.pack $
  concatMap (\(x,v) -> T.unpack (formToAtom v) ++ "{ " ++ T.unpack x ++ " " ++ "} ") binds
  ++ T.unpack (formToAtom body)
  
fthConName :: QName -> FthAtom
fthConName x = T.pack $ prettyShow $ qnameName x

fthPatternMatch :: FthForm -> [FthForm] -> Maybe FthForm -> FthForm
fthPatternMatch x cases maybeFallback  = RSList
  [RSAtom (makeForthy x cases maybeFallback)]
  -- ++
  -- [ RSList [ RSAtom "FALLBACK(?)" , fallback ] | fallback <- maybeToList maybeFallback
  -- ]
    where
      makeForthy :: FthForm -> [FthForm] -> Maybe FthForm -> FthAtom
      makeForthy arg (RSList [pat, RSList wildcards, expr]:xs) fallback = T.concat [
        T.concat [
          formToAtom arg,
          T.concat (map (\x -> T.pack "makeWILDCARD ") wildcards ++ [T.pack (init (T.unpack (formToAtom pat)) ++ " ")] ++ map (\x -> T.pack "pass ") wildcards),
          -- T.concat (map (\x -> T.pack "makeWILDCARD ") wildcards ++ [T.pack ( fixName (init $ T.unpack (formToAtom pat)) ++ " ")] ++ map (\x -> T.pack "pass ") wildcards),
          T.pack "0 pointer !",
          T.concat (T.pack (" obj= if wildcards " ++ show (length wildcards) ++ " pushArrayN { ") : map formToAtom wildcards ++ [T.pack "} "] ++ [T.pack newLine]),
          formToAtom expr
        ],
        T.pack " else ",
        makeForthy arg xs fallback,
        T.pack " then "
        ]
      makeForthy arg (RSList [guard, body]:xs) fallback = T.concat
        [ formToAtom guard
        , " if "
        , formToAtom body
        , " else "
        , makeForthy arg xs fallback
        , " then "
        ]
      makeForthy arg (other:xs) fallback = T.append
        (T.pack "ENCOUNTERED UNEXPECTED PATTERN WHEN COMPILING PATTERN MATCHING")
        (makeForthy arg xs fallback)
      makeForthy arg [] fallback = T.concat (map formToAtom (maybeToList fallback))

fthUnit :: FthForm
fthUnit = RSList [RSAtom "0"]

fthDelay :: FthForm -> FthForm
fthDelay x
  | RSList [y, RSAtom "dethunk"] <- x = y
  | otherwise                       = RSList [x, RSAtom "makeTHUNK"]

fthForce :: FthForm -> FthForm
fthForce x = RSList [x, RSAtom "deepdethunk"]


fthAdd, fthSub, fthMul, fthQuot, fthRem, fthIf, fthEq, fthGeq, fthLt :: FthForm
fthAdd  = RSList [RSAtom "add"]
fthSub  = RSList [RSAtom "sub"]
fthMul  = RSList [RSAtom "mul"]
fthQuot = RSList [RSAtom "quot"]
fthRem  = RSList [RSAtom "rem"]
fthIf   = RSList [RSAtom "iff"]
fthEq   = RSList [RSAtom "eq"]
fthGeq   = RSList [RSAtom "geq"]
fthLt   = RSList [RSAtom "lt"]

fthPreamble :: ToForthM [FthForm]
fthPreamble = do
  force <- makeForce
  return
    -- [ RSAtom "s\" ../lib/loader.fth\" included"
    [ fthSimpleWord "add"  $ fthLocals ["m","n"] $ RSAtom $ formToAtom $ RSList [force (RSAtom "m"), force (RSAtom "n"), RSAtom "+"]
    , fthSimpleWord "sub"  $ fthLocals ["m","n"] $ RSAtom $ formToAtom $ RSList [force (RSAtom "m"), force (RSAtom "n"), RSAtom "-"]
    , fthSimpleWord "mul"  $ fthLocals ["m","n"] $ RSAtom $ formToAtom $ RSList [force (RSAtom "m"), force (RSAtom "n"), RSAtom "*"]
    , fthSimpleWord "quot" $ fthLocals ["m","n"] $ RSAtom $ formToAtom $ RSList [force (RSAtom "m"), force (RSAtom "n"), RSAtom "/"]
    , fthSimpleWord "rem"  $ fthLocals ["m","n"] $ RSAtom $ formToAtom $ RSList [force (RSAtom "m"), force (RSAtom "n"), RSAtom "mod"]
    , fthSimpleWord "iff"  $ fthLocals ["b","x","y"] $ RSAtom $ formToAtom $ RSList [force (RSAtom "b"), RSAtom "if", force (RSAtom "x"), RSAtom "else", force (RSAtom "y"), RSAtom "then"]
    , fthSimpleWord "eq"   $ fthLocals ["x","y"] $ RSAtom $ formToAtom $ RSList [force (RSAtom "x"), force (RSAtom "y"), RSAtom "="]
    , fthSimpleWord "geq"  $ fthLocals ["x","y"] $ RSAtom $ formToAtom $ RSList [force (RSAtom "x"), force (RSAtom "y"), RSAtom ">="]
    , fthSimpleWord "lt"   $ fthLocals ["x","y"] $ RSAtom $ formToAtom $ RSList [force (RSAtom "x"), force (RSAtom "y"), RSAtom "<"]
    , fthSimpleWord "monus"$ fthLocals ["x","y"] $ RSAtom $ formToAtom $ RSList [force (RSAtom "y x sub pass pass"),  RSAtom "dup 0 < if drop 0 then"]
    ]

getFLib :: String
getFLib = unsafeLocalState readFLib

readFLib :: IO String
readFLib = do 
  fname <- getDataFileName "FLib.fth"
  readFile fname


deriving instance Generic EvaluationStrategy
deriving instance NFData  EvaluationStrategy

data FthOptions = FthOptions
  { fthEvaluation :: EvaluationStrategy
  }
  deriving (Generic, NFData)

data ToForthEnv = ToForthEnv
  { toForthOptions :: FthOptions
  , toForthVars    :: [FthAtom]
  }

initToForthEnv :: FthOptions -> ToForthEnv
initToForthEnv opts = ToForthEnv opts []

addVarBinding :: FthAtom -> ToForthEnv -> ToForthEnv
addVarBinding x env = env { toForthVars = x : toForthVars env }

data ToForthState = ToForthState
  { toForthFresh     :: [FthAtom]          -- Used for locally bound named variables
  , toForthDefs      :: Map QName FthAtom  -- Used for global definitions
  , toForthUsedNames :: Set FthAtom        -- Names that are already in use (both variables and definitions)
  }

-- This is an infinite supply of variable names
-- a, b, c, ..., z, a1, b1, ..., z1, a2, b2, ...
-- We never reuse variable names to make the code easier to
-- understand.
freshVars :: [FthAtom]
freshVars = concat [ map (<> i) xs | i <- "":map (T.pack . show) [1..] ]
  where
    xs = map T.singleton ['a'..'z']

-- These are names that should not be used by the code we generate
reservedNames :: Set FthAtom
reservedNames = Set.fromList $ map T.pack
  [ "loop" , "dethunk" , "obj=" , "obj=?"
  , "deepdethunk" , "print" , "shallowPrint"
  , "add", "sub", "mul", "quot", "rem"
  , "iff", "eq", "monus", "curry", "{", "}"
  , "(", ")"
  -- TODO: add more
  ]

initToForthState :: ToForthState
initToForthState = ToForthState
  { toForthFresh     = freshVars
  , toForthDefs      = Map.empty
  , toForthUsedNames = reservedNames
  }

type ToForthM a = StateT ToForthState (ReaderT ToForthEnv TCM) a

runToForthM :: FthOptions -> ToForthM a -> TCM a
runToForthM opts =
    (`runReaderT` initToForthEnv opts)
  . (`evalStateT` initToForthState)

freshFthAtom :: ToForthM FthAtom
freshFthAtom = do
  names <- gets toForthFresh
  case names of
    [] -> fail "No more variables!"
    (x:names') -> do
      modify $ \st -> st { toForthFresh = names' }
      ifM (isNameUsed x) freshFthAtom $ {-otherwise-} do
        setNameUsed x
        return x

getEvaluationStrategy :: ToForthM EvaluationStrategy
getEvaluationStrategy = reader $ fthEvaluation . toForthOptions

makeDelay :: ToForthM (FthForm -> FthForm)
makeDelay = return id

makeForce :: ToForthM (FthForm -> FthForm)
makeForce = return fthForce

getVarName :: Int -> ToForthM FthAtom
getVarName i = reader $ (!! i) . toForthVars

withFreshVar :: (FthAtom -> ToForthM a) -> ToForthM a
withFreshVar f = do
  x <- freshFthAtom
  local (addVarBinding x) $ f x

withFreshVars :: Int -> ([FthAtom] -> ToForthM a) -> ToForthM a
withFreshVars i f
  | i <= 0    = f []
  | otherwise = withFreshVar $ \x -> withFreshVars (i-1) (f . (x:))

saveDefName :: QName -> FthAtom -> ToForthM ()
saveDefName n a = modify $ \s -> s { toForthDefs = Map.insert n a (toForthDefs s) }

isNameUsed :: FthAtom -> ToForthM Bool
isNameUsed x = gets (Set.member x . toForthUsedNames)

setNameUsed :: FthAtom -> ToForthM ()
setNameUsed x = modify $ \s ->
  s { toForthUsedNames = Set.insert x (toForthUsedNames s) }

-- Extended alphabetic characters that are allowed to appear in
-- a Forth identifier
forthExtendedAlphaChars :: Set Char
forthExtendedAlphaChars = Set.fromList
  [ '!' , '$' , '%' , '&' , '*' , '+' , '-' , '.' , '/' , ':' , '<' , '=' , '>'
  , '?' , '@' , '^' , '_' , '~'
  ]

-- Categories of unicode characters that are allowed to appear in
-- a Forth identifier
forthAllowedUnicodeCats :: Set GeneralCategory
forthAllowedUnicodeCats = Set.fromList
  [ UppercaseLetter , LowercaseLetter , TitlecaseLetter , ModifierLetter
  , OtherLetter , NonSpacingMark , SpacingCombiningMark , EnclosingMark
  , DecimalNumber , LetterNumber , OtherNumber , ConnectorPunctuation
  , DashPunctuation , OtherPunctuation , CurrencySymbol , MathSymbol
  , ModifierSymbol , OtherSymbol , PrivateUse
  ]

-- True if the character is allowed to be used in a Forth word
isValidForthChar :: Char -> Bool
isValidForthChar x
  =  x /= ' '
  && x /= '\n'
  && x /= '\t'

-- Creates a valid Forth name from a (qualified) Agda name.
-- Precondition: the given name is not already in toForthDefs.
makeForthName :: QName -> ToForthM FthAtom
makeForthName n = do
  a <- go $ fixName $ prettyShow $ qnameName n
  saveDefName n a
  setNameUsed a
  return a
  where
    nextName = ('z':) -- TODO: do something smarter

    go s     = ifM (isNameUsed $ T.pack s) (go $ nextName s) (return $ T.pack s)

fixName :: Foldable t => t Char -> [Char]
fixName s =
  let s' = concatMap fixChar s in
  if isNumber (head s') then "z" ++ s' else s'

fixChar :: Char -> [Char]
fixChar c
  | isValidForthChar c = [c]
  | otherwise           = "\\x" ++ toHex (ord c) ++ ";"

toHex :: Int -> [Char]
toHex 0 = ""
toHex i = toHex (i `div` 16) ++ [fourBitsToChar (i `mod` 16)]

fourBitsToChar :: Int -> Char
fourBitsToChar i = "0123456789ABCDEF" !! i
{-# INLINE fourBitsToChar #-}

class ToForth a b where
  toForth :: a -> ToForthM b

instance ToForth QName FthAtom where
  toForth n = do
    r <- gets (Map.lookup n . toForthDefs)
    case r of
      Nothing -> makeForthName n
      Just a  -> return a

instance ToForth Definition (Maybe FthForm) where
  toForth def
    | defNoCompilation def ||
      not (usableModality $ getModality def) = return Nothing
  toForth def = do
    let f = defName def
    case theDef def of
      Axiom{} -> do
        return $ Just $ RSAtom ""
      GeneralizableVar{} -> return Nothing
      d@Function{} | d ^. funInline -> return Nothing
      Function{} -> do
        f' <- toForth f
        strat <- getEvaluationStrategy
        maybeCompiled <- liftTCM $ toTreeless strat f
        case maybeCompiled of
          Just body -> Just . fthWord f' <$> toForth body
          Nothing   -> return Nothing
      Primitive{} -> do
        f' <- toForth f
        return $ Just $ fthAxiom f' -- TODO!
      PrimitiveSort{} -> return Nothing
      Datatype{} -> return Nothing
      Record{} -> return Nothing
      Constructor{ conSrcCon = chead, conArity = nargs } -> do
        let c = conName chead
        c' <- toForth c
        withFreshVars nargs $ \xs ->
          return $ Just $ fthDefineType c' (length xs) (fthConstructor c' (length xs))

      AbstractDefn{} -> __IMPOSSIBLE__
      DataOrRecSig{} -> __IMPOSSIBLE__


instance ToForth TTerm FthForm where
  toForth v = do
    -- v <- liftTCM $ eliminateLiteralPatterns (convertGuards v)
    let (w, args) = tAppView v
    delay <- makeDelay
    args' <- map delay <$> traverse toForth args
    let applyToArgs f = return $ fthApps f args'
    case w of
      TVar i -> do
          name <- getVarName i
          -- force <- makeForce
          -- applyToArgs $ force $ RSAtom name
          applyToArgs $ RSAtom name
      TPrim p -> toForth p >>= applyToArgs
      TDef d -> do
        special <- isSpecialDefinition d
        case special of
          Nothing -> do
            d' <- toForth d
            applyToArgs $ RSList [RSAtom d']
          Just v -> applyToArgs v
      TLam v -> withFreshVar $ \x -> do
        unless (null args) __IMPOSSIBLE__
        body <- toForth v
        withFreshVars (countLambdas body) $ \y -> do
          applyToArgs $ fthLambda [x] y body
      TLit l -> do
        unless (null args) __IMPOSSIBLE__
        toForth l
      TCon c -> do
        special <- isSpecialConstructor c
        case special of
          Nothing -> do
            c' <- toForth c
            applyToArgs $ RSList [RSAtom c']
          Just v  -> applyToArgs v
      TLet u v -> do
        unless (null args) __IMPOSSIBLE__
        expr <- toForth u
        withFreshVar $ \x -> do
          body <- toForth v
          applyToArgs $ fthLet [(x,expr)] body
      TCase i info v bs -> do
        unless (null args) __IMPOSSIBLE__
        -- force <- makeForce
        -- x <- force . RSAtom <$> getVarName i
        x <- RSAtom <$> getVarName i
        cases <- traverse toForth bs
        -- fallback <- if isUnreachable v
        --     then return Nothing
        --     else Just <$> toForth v
        -- applyToArgs $ fthPatternMatch x cases fallback
        special <- isSpecialCase info
        case special of
          Nothing -> do
            fallback <- if isUnreachable v
                        then return Nothing
                        else Just <$> toForth v
            applyToArgs $ fthPatternMatch x cases fallback
          Just BoolCase -> case bs of
            [] -> __IMPOSSIBLE__
            (TACon c1 _ v1 : bs') -> do
              Con trueC  _ _ <- primTrue
              Con falseC _ _ <- primFalse
              v1' <- toForth v1
              v2' <- case bs' of
                []                 -> toForth v
                (TACon _ _ v2 : _) -> toForth v2
                _                  -> __IMPOSSIBLE__
              let (thenBranch,elseBranch)
                    | c1 == conName trueC  = (v1',v2')
                    | c1 == conName falseC = (v2',v1')
                    | otherwise            = __IMPOSSIBLE__
              applyToArgs $ RSList [x, RSAtom "if", thenBranch, RSAtom "else", elseBranch, RSAtom "then"]
            _ -> return $ RSAtom "ERRONEOUS BOOLCASE DURING CASE MATCHING"

      TUnit -> do
        unless (null args) __IMPOSSIBLE__
        return fthUnit
      TSort -> do
        unless (null args) __IMPOSSIBLE__
        return fthUnit
      TErased -> return fthUnit
      TCoerce u -> applyToArgs =<< toForth u
      TError err -> toForth err
      TApp f args -> __IMPOSSIBLE__

    where
      isUnreachable v = v == TError TUnreachable

instance ToForth TPrim FthForm where
  toForth p = case p of
    PAdd  -> return fthAdd
    PSub  -> return fthSub
    PMul  -> return fthMul
    PQuot -> return fthQuot
    PRem  -> return fthRem
    PIf   -> return fthIf
    PEqI  -> return fthEq
    PGeq  -> return fthGeq
    PLt   -> return fthLt
    _     -> return $ fthError $ T.pack $ "not yet supported: primitive " ++ show p

instance ToForth Literal FthForm where
  toForth lit = case lit of
    LitNat    x -> return $ RSAtom (T.pack (show x))
    LitWord64 x -> return $ fthError "not yet supported: Word64 literals"
    LitFloat  x -> return $ fthError "not yet supported: Float literals"
    LitString x -> return $ fthError "not yet supported: String literals"
    LitChar   x -> return $ fthError "not yet supported: Char literals"
    LitQName  x -> return $ fthError "not yet supported: QName literals"
    LitMeta p x -> return $ fthError "not yet supported: Meta literals"


-- TODO: allow literal branches and guard branches
instance ToForth TAlt FthForm where
  toForth alt = case alt of
    TACon c nargs v -> withFreshVars nargs $ \xs -> do
      body <- toForth v
      return $ RSList [RSList [RSAtom (fthConName c)], RSList (map RSAtom xs), body]

    TAGuard guard body -> do
      guard <- toForth guard
      body <- toForth body
      return $ RSList [guard, body]

    TALit lit body -> do
      lit <- toForth lit
      body <- toForth body
      return $ RSList [lit, RSList [], body]

instance ToForth TError FthForm where
  toForth err = case err of
    TUnreachable -> return $ fthError "Panic!"
    TMeta s      -> return $ fthError $ "encountered unsolved meta: " <> T.pack s

isSpecialConstructor :: QName -> ToForthM (Maybe FthForm)
isSpecialConstructor c = do
  Con trueCon  _ _ <- primTrue
  Con falseCon _ _ <- primFalse
  if | c == conName trueCon  -> return $ Just $ RSAtom (T.pack $ show (-1))
     | c == conName falseCon -> return $ Just $ RSAtom (T.pack $ show 0)
     | otherwise             -> return Nothing

isSpecialDefinition :: QName -> ToForthM (Maybe FthForm)
isSpecialDefinition f = do
  minusDef <- getBuiltinName builtinNatMinus
  if | Just f == minusDef -> return $ Just $ RSList [RSAtom "monus"]
     | otherwise          -> return Nothing

-- Some kinds of case statements are treated in a special way.
-- Currently, matches on Bool are translated to an `if` statement.
data SpecialCase = BoolCase

isSpecialCase :: CaseInfo -> ToForthM (Maybe SpecialCase)
isSpecialCase (CaseInfo lazy (CTData q cty)) = do
  boolTy <- primBool
  if boolTy == Def cty []
    then return (Just BoolCase)
    else return Nothing
isSpecialCase _ = return Nothing

makeDefines :: Text -> Text
makeDefines x = T.append (T.pack defines) x
  where
    defines = concat (map (\y -> "defer " ++ y ++ "\n") (findAssignments (T.unpack x)))

findAssignments :: String -> [String]
findAssignments (' ':'i':'s':' ':rest) = name:(findAssignments rest2)
  where
    (name, rest2) = getAssignment rest
findAssignments (x:rest) = findAssignments rest
findAssignments [] = []

getAssignment :: String -> (String, String)
getAssignment ('\n':rest) = ([], rest)
getAssignment [] = ([], [])
getAssignment (x:rest) = ((x:xs), rest2)
  where
      (xs, rest2) = getAssignment rest
