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

import Control.Monad.IO.Class
import Control.Effect
import Control.Effect.Carrier
import Control.Effect.Error
import Control.Effect.Reader
import Control.Effect.State

import qualified Data.Map as M

import Expr
import Base
import Record
import Anf
import IO
import Utils

type PrimTypes = '[BasePrim, RecordPrim, AnfPrim, IOPrim]
type ValueTypes = '[LambdaValue (Eval IO), BaseValue, RecordValue, AnfValue]

newtype Eval m a = Eval
  { unEval :: ErrorC String (ReaderC (M.Map Var (Value ValueTypes)) (StateC EVar (LiftC m))) a
  } deriving (Functor, Applicative, Monad, MonadIO)

instance (MonadIO m) => Carrier (Error String :+: Reader (M.Map Var (Value ValueTypes)) :+: State EVar :+: Lift m) (Eval m) where
  eff x = Eval $ eff (hmap unEval x)

runEval :: Eval IO a -> IO (Either String a)
runEval k = runM . evalState 100 . runReader M.empty . runError . unEval $ k

eval' :: Expr PrimTypes -> Eval IO (Value ValueTypes)
eval' a = eval a

test1 :: (BasePrim :<< p, RecordPrim :<< p, AnfPrim :<< p) => Expr p
test1 =
  let_ 0 (lit (-3.14))
  $ let_ 1 (prim Add ! lit 10 ! var 0)
  $ let_ 2 (cnst (var 1))
  $ let_ 3 (var 2 `eadd` var 2)
  $ var 2 `eadd` (prim If ! var 0 ! var 2 ! var 3)

test2 :: (BasePrim :<< p, RecordPrim :<< p, AnfPrim :<< p) => Expr p
test2 =
  loop $ lam 1 $
    loop $ lam 2 $
      var 1 **
      var 2 **
      cnst (lit 30)

test3 :: Expr PrimTypes
test3 =
  let_ 1
    ( rext "bar" (cnst (lit 1)) $
      rext "foo" (readln) $
      rnil ) $
    writeln (rsel "foo" (var 1))

main :: IO ()
main =
  return ()
