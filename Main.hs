{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}

module Main (main) where

import Prelude hiding ((**))

import System.Environment
import System.Exit

import Control.Effect
import Control.Effect.Carrier
import Control.Effect.Error
import Control.Effect.Reader
import Control.Monad.IO.Class

import qualified Data.ByteString.Lazy.Char8 as B8
import Data.Text.Prettyprint.Doc
import qualified Language.SexpGrammar

import Errors
import Eval
import Expr
import Pretty
import Prim.Anf
import Prim.Base
import Prim.Exception
import Prim.IO
import Prim.Link
import Prim.Record
import Prim.Variant
import Syntax.Sugared (desugar, sugaredGrammar)
import TypeChecker
import Types

----------------------------------------------------------------------
-- Concrete language

type PrimTypes = '[BasePrim, RecordPrim, VariantPrim, AnfPrim, IOPrim, LinkPrim, ExceptionPrim]
type ValueTypes = '[LambdaValue (Eval IO), BaseValue, RecordValue, VariantValue,AnfValue]

newtype Eval m a = Eval
  { unEval :: RuntimeErrorEffectC (ExceptionEffectC ValueTypes (EnvEffectC ValueTypes (AnfEffectC (LiftC m)))) a
  } deriving (Functor, Applicative, Monad, MonadIO)

instance (MonadIO m) => Carrier
    ( RuntimeErrorEffect
      :+: ExceptionEffect ValueTypes
      :+: EnvEffect ValueTypes
      :+: AnfEffect
      :+: Lift m
    ) (Eval m) where
  eff x = Eval $ eff (hmap unEval x)

runEval :: Eval IO a -> IO (Either String a)
runEval k = do
  result <- runM . runAnf . runEnv . runException . runRuntimeError . unEval $ k
  pure $ case result of
    Left unhandledException -> Left (render $ nest 2 $ vsep ["Unhandled exception:", ppValue unhandledException])
    Right (Left runtimeError) -> Left runtimeError
    Right (Right res) -> Right res

eval' :: Expr PrimTypes -> IO (Either String (Value ValueTypes))
eval' e = runEval (eval e)

infer' :: Expr PrimTypes -> Either TCError (Type, Type)
infer' a = runInfer (inferExprType a)

----------------------------------------------------------------------

main :: IO ()
main = do
  args <- getArgs
  (fn, str) <-
    case args of
      []   -> (,) <$> pure "<stdin>" <*> B8.getContents
      [fn] -> (,) <$> pure fn <*> B8.readFile fn
      _    -> die "USAGE: lf [file]"
  expr <-
    case Language.SexpGrammar.decodeWith sugaredGrammar fn str of
      Left err -> die $ "parse error:\n" ++ err
      Right s -> pure (desugar s :: Expr PrimTypes)

  putStrLn $ render (ppExpr expr)

  case infer' expr of
    Left tcerror -> die (render (ppError tcerror))
    Right (ty,effty) -> do
      putStrLn $ render $ vsep
        [ "----------------------------------------------------------------------"
        , ":" <+> ppType ty
        , "!" <+> ppType effty
        , "----------------------------------------------------------------------"
        ]
      res <- eval' expr
      case res of
        Left err -> putStrLn err
        Right p -> putStrLn (render (ppValue p))
