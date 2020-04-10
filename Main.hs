{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE TypeOperators              #-}

module Main (main) where

import qualified System.IO as IO
import System.Exit

import Control.Effect
import Control.Effect.Carrier
import Control.Effect.Error
import Control.Effect.Reader
import Control.Monad (unless, forM_)
import Control.Monad.IO.Class

import qualified Data.ByteString.Lazy.Char8 as B8
import Data.Text.Prettyprint.Doc
import qualified Language.SexpGrammar
import qualified Language.Sexp.Located

import qualified Options.Applicative as Opt

import Errors
import Eval
import Expr
import Pretty
import Prim.Base
import Prim.Exception
import Prim.IO
import Prim.Kappa
import Prim.Link
import Prim.Record
import Prim.Variant
import Syntax.Sugared (desugar, sugaredGrammar)
import TypeChecker (runInfer, inferExprType)
import Types (Type)

----------------------------------------------------------------------
-- Concrete language

type PrimTypes = '[BasePrim, RecordPrim, VariantPrim, KappaPrim, IOPrim, LinkPrim, ExceptionPrim]
type ValueTypes = '[LambdaValue (Eval IO), BaseValue, RecordValue, VariantValue, KappaValue]

newtype Eval m a = Eval
  { unEval :: RuntimeErrorEffectC (ExceptionEffectC ValueTypes (EnvEffectC ValueTypes (KappaEffectC (LiftC m)))) a
  } deriving (Functor, Applicative, Monad, MonadIO)

instance (MonadIO m) => Carrier
    ( RuntimeErrorEffect
      :+: ExceptionEffect ValueTypes
      :+: EnvEffect ValueTypes
      :+: KappaEffect
      :+: Lift m
    ) (Eval m) where
  eff x = Eval $ eff (hmap unEval x)

runEval :: Eval IO a -> IO (Either String a)
runEval k = do
  result <- runM . runKappa . runEnv . runException . runRuntimeError . unEval $ k
  pure $ case result of
    Left unhandledException -> Left (render $ nest 2 $ vsep ["Unhandled exception:", ppValue unhandledException])
    Right (Left runtimeError) -> Left runtimeError
    Right (Right res) -> Right res

eval' :: Expr PrimTypes -> IO (Either String (Value ValueTypes))
eval' e = runEval (eval e)

infer' :: Expr PrimTypes -> Either TCError Type
infer' a = runInfer (inferExprType a)

----------------------------------------------------------------------

data Options = Options
  { optTypecheck :: Bool
  , optFilename  :: Maybe FilePath
  }

parseOptions :: Opt.Parser Options
parseOptions =
  Options
    <$> (Opt.switch $
           Opt.long "check" <>
           Opt.help "Typecheck only")
    <*> (Opt.optional $ Opt.strArgument $
           Opt.metavar "SRC" <>
          Opt.help "Source .lf file to process (run or typecheck)")

main :: IO ()
main = do
  IO.hSetEncoding IO.stdin  IO.utf8
  IO.hSetEncoding IO.stdout IO.utf8
  IO.hSetEncoding IO.stderr IO.utf8

  Options{..} <- Opt.execParser $
    Opt.info
      (Opt.helper <*> parseOptions)
      (Opt.fullDesc <>
       Opt.progDesc "Lambda F interpreter")

  (fn, str) <-
    case optFilename of
      Nothing -> (,) <$> pure "<stdin>" <*> B8.getContents
      Just fn -> (,) <$> pure fn <*> B8.readFile fn

  exprs <-
    case Language.Sexp.Located.parseSexps fn str >>=
         traverse (Language.SexpGrammar.fromSexp sugaredGrammar)
    of
      Left err -> die $ "parse error:\n" ++ err
      Right s -> pure (map desugar s :: [Expr PrimTypes])

  forM_ exprs $ \expr -> do
    unless optTypecheck $
      putStrLn $ render (ppExpr expr)

    case infer' expr of
      Left tcerror ->
        IO.hPutStrLn IO.stderr
          (render (ppError tcerror))

      Right ty -> do
        unless optTypecheck $ putStrLn $ render $ vsep
          [ "----------------------------------------------------------------------"
          , ":" <+> ppType ty
          , "----------------------------------------------------------------------"
          ]
        unless optTypecheck $ do
          res <- eval' expr
          case res of
            Left err -> putStrLn err
            Right p -> putStrLn (render (ppValue p))
