module Main where

import Prelude hiding ( null , empty )

import Agda.Compiler.Backend
import Agda.Compiler.Common

import Agda.Main ( runAgda )

-- import Agda.Compiler.ToScheme
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

backend' :: Backend' SchOptions SchOptions () () (Maybe SchForm)
backend' = Backend'
  { backendName           = "agda2scheme"
  , options               = SchOptions EagerEvaluation
  , commandLineFlags      = schFlags
  , isEnabled             = \ _ -> True
  , preCompile            = schPreCompile
  , postCompile           = \ _ _ _ -> return ()
  , preModule             = \ _ _ _ _ -> return $ Recompile ()
  , compileDef            = schCompileDef
  , postModule            = schPostModule
  , backendVersion        = Nothing
  , scopeCheckingSuffices = False
  , mayEraseType          = \ _ -> return True
  }

schFlags :: [OptDescr (Flag SchOptions)]
schFlags =
  [ Option [] ["lazy-evaluation"] (NoArg $ evaluationFlag LazyEvaluation)
              "Insert delay and force operations to enable lazy evaluation"
  , Option [] ["strict-evaluation"] (NoArg $ evaluationFlag EagerEvaluation)
              "Do not insert delay and force operations (default)"
  ]

schPreCompile :: SchOptions -> TCM SchOptions
schPreCompile opts = return opts

schCompileDef :: SchOptions -> () -> IsMain -> Definition -> TCM (Maybe SchForm)
schCompileDef opts _ isMain def = runToSchemeM opts $ toScheme def

schPostModule :: SchOptions -> () -> IsMain -> ModuleName -> [Maybe SchForm] -> TCM ()
schPostModule opts _ isMain modName defs = do
  preamble <- runToSchemeM opts fthPreamble
  let defToText = encodeOne printer . fromRich
      modText   = makeDefines
        (T.intercalate "\n\n" $
        map (
            (\x -> T.pack (snd (moveLambdas (T.unpack x) []))) .
            defToText
        ) 
          (preamble ++ catMaybes defs))
      fileName  = prettyShow (last $ mnameToList modName) ++ ".fth"
  liftIO $ T.writeFile fileName modText

  where
    printer :: SExprPrinter Text (SExpr Text)
    printer = basicPrint id

evaluationFlag :: EvaluationStrategy -> Flag SchOptions
evaluationFlag s o = return $ o { schEvaluation = s }
