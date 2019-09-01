{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MonoLocalBinds             #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}

module Eval
  ( RuntimeErrorEffect
  , RuntimeErrorEffectC
  , runRuntimeError
  , evalError
  , EnvEffect
  , EnvEffectC
  , localEnv
  , askEnv
  , runEnv
  , EvalPrim (..)
  , eval
  ) where

import Control.Effect.Error
import Control.Effect.Reader

import Data.Functor.Const
import Data.Functor.Foldable (unfix, cata)
import qualified Data.Map as M
import Data.Sum
import Data.Void
import Data.Coerce

import Expr
import Utils

newtype RuntimeError = RuntimeError String
type RuntimeErrorEffect = Error RuntimeError
type RuntimeErrorEffectC = ErrorC RuntimeError

evalError :: (Member RuntimeErrorEffect sig, Carrier sig m) => String -> m a
evalError = throwError . RuntimeError . ("Runtime error: " ++)

runRuntimeError :: (Monad m) => RuntimeErrorEffectC m a -> m (Either String a)
runRuntimeError = fmap coerce . runError

newtype Env v = Env (M.Map Variable (Value v))
type EnvEffect v = Reader (Env v)
type EnvEffectC v = ReaderC (Env v)

runEnv :: EnvEffectC v m a -> m a
runEnv = runReader (Env M.empty)

localEnv
  :: (Member (EnvEffect v) sig, Carrier sig m) =>
     (M.Map Variable (Value v) -> M.Map Variable (Value v))
  -> m a -> m a
localEnv f = local (\(Env m) -> Env . f $ m)

askEnv :: (Member (EnvEffect v) sig, Carrier sig m) => Variable -> m (Maybe (Value v))
askEnv x = asks (\(Env m) -> M.lookup x m)

class EvalPrim m v (p :: * -> *) where
  evalPrim :: p Void -> m (Value v)

instance (Apply (EvalPrim m v) ps) => EvalPrim m v (Sum ps) where
  evalPrim = apply @(EvalPrim m v) evalPrim

eval :: forall m sig (p :: [*]) (v :: [* -> *]).
  ( Member (RuntimeErrorEffect) sig
  , Member (EnvEffect v) sig
  , Carrier sig m
  , EvalPrim m v (Sum (Map Const p))
  , LambdaValue m :< v
  ) => Expr p -> m (Value v)
eval = cata alg
  where
    alg :: ExprF p (m (Value v)) -> m (Value v)
    alg = \case
      Ref pos x -> do
        v <- askEnv x
        case v of
          Nothing -> evalError $ show pos ++ ": Variable not found: " ++ show x
          Just v' -> pure v'

      Lambda _pos x body -> do
        Env env <- ask
        let f v = localEnv (\_ -> M.insert x v env) body
        pure $ mkVLam @m f

      App pos f e -> do
        f' <- f
        case project (unfix f') of
          Just (VLam f'') -> e >>= f''
          _ -> evalError $ show pos ++ ": Could not apply to a non-function"

      Let _pos x e body -> do
        v <- e
        localEnv (M.insert x v) body

      Prim _pos p ->
        evalPrim p
