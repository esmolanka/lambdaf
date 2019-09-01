{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeOperators              #-}
-- :-/
{-# LANGUAGE UndecidableInstances       #-}

module Main where

import Prelude hiding ((**))

import System.Environment
import System.Exit

import Control.Monad.IO.Class
import Control.Effect
import Control.Effect.Carrier
import Control.Effect.Error
import Control.Effect.Reader
import Control.Effect.State

import qualified Data.ByteString.Lazy.Char8 as B8
import qualified Data.Map as M

import qualified Language.SexpGrammar

import Errors
import Expr
import Pretty
import Prim.Anf
import Prim.Base
import Prim.IO
import Prim.Record
import Syntax.Sugared (desugar, sugaredGrammar)
import TypeChecker
import Types

type PrimTypes = '[BasePrim, RecordPrim, AnfPrim, IOPrim]
type ValueTypes = '[LambdaValue (Eval IO), BaseValue, RecordValue, AnfValue]

newtype Eval m a = Eval
  { unEval :: ErrorC String (ReaderC (M.Map Variable (Value ValueTypes)) (StateC EVar (LiftC m))) a
  } deriving (Functor, Applicative, Monad, MonadIO)

instance (MonadIO m) => Carrier (Error String :+: Reader (M.Map Variable (Value ValueTypes)) :+: State EVar :+: Lift m) (Eval m) where
  eff x = Eval $ eff (hmap unEval x)

runEval :: Eval IO a -> IO (Either String a)
runEval k = runM . evalState 100 . runReader M.empty . runError . unEval $ k

eval' :: Expr PrimTypes -> IO (Either String (Value ValueTypes))
eval' e = runEval (eval e)

infer' :: Expr PrimTypes -> Either TCError (Type, Type)
infer' a = runInfer (inferExprType a)

----------------------------------------------------------------------

evalExpr :: Expr PrimTypes -> IO ()
evalExpr e = do
  res <- eval' e
  case res of
    Left err -> putStrLn err
    Right p -> putStrLn (render (ppValue p))

typeExpr :: Expr PrimTypes -> IO ()
typeExpr e = do
  case infer' e of
    Left err -> putStrLn (render (ppError err))
    Right (ty,effty) -> putStrLn $ render (ppType ty) ++ "\n" ++ render (ppType effty)

----------------------------------------------------------------------

test1 :: Expr PrimTypes
test1 =
  let_ 0 (writeln (txt "Enter a number: "))
  $ let_ 0 (prim ReadDouble ! readln)
  $ let_ 1 (prim Add ! lit 10 ! var 0)
  $ let_ 2 (cnst (var 1))
  $ let_ 3 (var 2 `eadd` var 2)
  $ var 2 `eadd` (prim If ! var 0 ! (lam 0 (var 2)) ! (lam 0 (var 3)))

test2 :: Expr PrimTypes
test2 =
  loop $ lam 1 $
    loop $ lam 2 $
      var 1 **
      var 2 **
      cnst (lit 30)

test3 :: Expr PrimTypes
test3 =
  let_ 1
    ( rext "bar" (lit 1) $
      rext "foo" (readln) $
      rnil ) $
    writeln (rsel "foo" (var 1))

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
      putStrLn $ " : " ++ render (ppType ty) ++ "\nε: " ++ render (ppType effty)
      evalExpr expr
