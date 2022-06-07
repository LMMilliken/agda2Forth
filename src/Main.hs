module Main where

import Prelude hiding ( null , empty )

import Agda.Compiler.Backend
import Agda.Compiler.Common

import Agda.Main ( runAgda )

import Agda.Compiler.ToForth

import Agda.Interaction.Options ( OptDescr(..) , ArgDescr(..) )

import Agda.Syntax.Treeless ( EvaluationStrategy(..) )

import Agda.TypeChecking.Pretty

import Agda.Utils.Either
import Agda.Utils.Functor
import Agda.Utils.Null
import Agda.Utils.Pretty ( prettyShow )

import Control.DeepSeq ( NFData )

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer

import Data.Function
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.SCargot
import Data.SCargot.Repr
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as T

import GHC.Generics ( Generic )

main :: IO ()
main = runAgda [backend]

backend :: Backend
backend = Backend backend'

backend' :: Backend' FthOptions FthOptions () () (Maybe FthForm)
backend' = Backend'
  { backendName           = "agda2forth"
  , options               = FthOptions EagerEvaluation
  , commandLineFlags      = fthFlags
  , isEnabled             = \ _ -> True
  , preCompile            = fthPreCompile
  , postCompile           = \ _ _ _ -> return ()
  , preModule             = \ _ _ _ _ -> return $ Recompile ()
  , compileDef            = fthCompileDef
  , postModule            = fthPostModule
  , backendVersion        = Nothing
  , scopeCheckingSuffices = False
  , mayEraseType          = \ _ -> return True
  }

fthFlags :: [OptDescr (Flag FthOptions)]
fthFlags =
  [ Option [] ["lazy-evaluation"] (NoArg $ evaluationFlag LazyEvaluation)
              "Insert delay and force operations to enable lazy evaluation"
  , Option [] ["strict-evaluation"] (NoArg $ evaluationFlag EagerEvaluation)
              "Do not insert delay and force operations (default)"
  ]

fthPreCompile :: FthOptions -> TCM FthOptions
fthPreCompile = return

fthCompileDef :: FthOptions -> () -> IsMain -> Definition -> TCM (Maybe FthForm)
fthCompileDef opts _ isMain def = runToForthM opts $ toForth def

fthPostModule :: FthOptions -> () -> IsMain -> ModuleName -> [Maybe FthForm] -> TCM ()
fthPostModule opts _ isMain modName defs = do
  preamble <- runToForthM opts fthPreamble
  let defToText = encodeOne printer . fromRich
      modText   = T.append 
        (T.pack getFLib) 
        (makeDefines
          (T.intercalate "\n\n" $
          map (
              fixWord .
              defToText
          )
            (preamble ++ catMaybes defs)))
      fileName  = prettyShow (last $ mnameToList modName) ++ ".fth"
  liftIO $ T.writeFile fileName modText

  where
    printer :: SExprPrinter Text (SExpr Text)
    printer = basicPrint id

evaluationFlag :: EvaluationStrategy -> Flag FthOptions
evaluationFlag s o = return $ o { fthEvaluation = s }
