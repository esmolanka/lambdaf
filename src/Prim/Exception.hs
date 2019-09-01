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
  ( ExceptionPrim (..)
  ) where

import Control.Effect.Carrier
import Control.Effect.Error

import Data.Functor.Classes
import Data.Functor.Const
import Data.Functor.Foldable (Fix (..), unfix)
import qualified Data.Map as M
import Data.Sum
import qualified Data.Text as T
import Data.Text.Prettyprint.Doc as PP

import Expr
import Pretty
import Syntax.Position
import Prim.Base
import Types
import Utils

data ExceptionPrim
  = RaiseExc
  | CatchExc

instance PrettyPrim (Const ExceptionPrim) where
  prettyPrim = \case
    Const RaiseExc -> "RaiseExc"
    Const CatchExc -> "CatchExc"

instance ( Member (Error String) sig
         , Member (Error (Value v)) sig
         , Carrier sig m
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
      projLam = project @(LambdaValue m) . unfix

exceptionEff :: Label
exceptionEff = Label "exc"

instance TypePrim (Const ExceptionPrim) where
  typePrim = \case
    Const CatchExc ->
      forall Star $ \a ->
      forall Star $ \b ->
      forall Star $ \c ->
      forall Presence $ \p ->
      effect $ \e1 ->
      effect $ \e2 ->
      mono $
        ((Fix $ T TUnit, Fix $ TRowExtend exceptionEff (Fix TPresent) b e2) ~> a, e1) ~>
        ((b, Fix (TRowExtend exceptionEff p c e2)) ~> a, Fix (TRowExtend exceptionEff p c e2)) ~>
        a
    Const RaiseExc ->
      forall Star $ \a ->
      forall Star $ \b ->
      effect $ \e ->
      mono $
        (a, Fix $ TRowExtend exceptionEff (Fix TPresent) a e) ~>
        b
