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

module Prim.Exception
  ( ExceptionEffect
  , ExceptionEffectC
  , runException
  , ExceptionPrim (..)
  ) where

import Control.Algebra
import Control.Effect.Error
import Control.Carrier.Error.Either

import Data.Functor.Const
import Data.Fix (Fix (..))
import Data.Sum

import Expr
import Eval
import Prim.Base
import Types
import Utils

type ExceptionEffect v = Error (Value v)
type ExceptionEffectC v = ErrorC (Value v)

runException :: ExceptionEffectC v m a -> m (Either (Value v) a)
runException = runError

data ExceptionPrim
  = RaiseExc
  | CatchExc

instance Pretty ExceptionPrim where
  pretty = \case
    RaiseExc -> "RaiseExc"
    CatchExc -> "CatchExc"

instance ( Has (RuntimeErrorEffect) sig m
         , Has (ExceptionEffect v) sig m
         , LambdaValue m :< v
         , BaseValue :< v
         ) => EvalPrim m v (Const ExceptionPrim) where
  evalPrim = \case
      Const RaiseExc ->
        pure $ mkVLam @m $ \e ->
          throwError e

      Const CatchExc ->
        pure $ mkVLam @m $ \k ->
        pure $ mkVLam @m $ \h ->
          case projLam k of
            Just (VLam k') ->
              catchError (k' mkVUnit) $ \e ->
                case projLam h of
                  Just (VLam h') -> h' e
                  Nothing -> evalError "Handler is not a function"
            Nothing -> evalError "Action is not a function"
    where
      projLam :: (LambdaValue m :< v) => Value v -> Maybe (LambdaValue m (Value v))
      projLam = project @(LambdaValue m) . unFix

instance TypePrim t (Const ExceptionPrim) where
  typePrim = \case
    Const CatchExc ->
      forall Star $ \a ->
      forall Star $ \b ->
      mono $
        (Fix TUnit ~> a) ~>
        (b ~> a) ~>
        a
    Const RaiseExc ->
      forall Star $ \a ->
      forall Star $ \b ->
      mono $
        a ~> b
