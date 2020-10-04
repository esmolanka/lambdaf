{-# LANGUAGE ConstraintKinds            #-}
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

module Prim.Dyn
  ( DynEnvEffect
  , DynAllocEffect
  , DynEffectC
  , runDyn
  , DynValue
  , DynType(..)
  , typeParameterOf
  , DynPrim(..)
  ) where

import Control.Effect.Carrier
import Control.Effect.Fail
import Control.Effect.State
import Control.Effect.Reader

import Data.Functor.Const
import Data.Functor.Foldable (Fix (..), unfix)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IM
import Data.Sum
import Data.Text.Prettyprint.Doc as PP

import Expr
import Eval
import Prim.Base
import Types
import Utils

newtype DVar = DVar Int

data DynEnv v = DynEnv (IntMap (Value v))

lookupEnv :: DVar -> DynEnv v -> Maybe (Value v)
lookupEnv (DVar n) (DynEnv m) = IM.lookup n m

updateEnv :: DVar -> Value v -> DynEnv v -> DynEnv v
updateEnv (DVar n) v (DynEnv m) = DynEnv (IM.insert n v m)

newtype DynState = DynState Int

type WithDynEffect v sig =
  ( Member (Reader (DynEnv v)) sig
  , Member (State DynState) sig
  )

type DynEnvEffect v = Reader (DynEnv v)
type DynAllocEffect = State DynState

type DynEffectC v m = StateC DynState (ReaderC (DynEnv v) m)

runDyn :: (Monad m) => DynEffectC v m a -> m a
runDyn = runReader (DynEnv mempty) . evalState (DynState 0)

data DynValue e
  = VDynVar DVar e

instance Pretty1 DynValue where
  liftPretty pp = \case
    VDynVar (DVar n) def -> "DynVar" <> braces (pretty n <+> "|" <+> pp def)

mkVDynVar :: (DynValue :< v) => DVar -> Value v -> Value v
mkVDynVar x def = Fix . inject $ VDynVar x def

projDynVar :: (DynValue :< v) => Value v -> Maybe (DynValue (Value v))
projDynVar = project @DynValue . unfix

data DynType
  = DTParameter
  | DTGlobal
    deriving (Eq, Show)

instance Pretty DynType where
  pretty = \case
    DTParameter -> "Parameter"
    DTGlobal -> "Global"

instance KindOfCtor (Const DynType) where
  kindOfCtor = \case
    Const DTParameter -> Region `Arr` Star `Arr` Star
    Const DTGlobal -> Region

data DynPrim
  = NewVar
  | NewGlobalVar
  | AskVar
  | SetVar

instance Pretty DynPrim where
  pretty = \case
    NewVar -> "NewVar"
    NewGlobalVar -> "NewGlobalVar"
    AskVar -> "AskVar"
    SetVar -> "SetVar"

instance ( MonadFail m
         , Member RuntimeErrorEffect sig
         , WithDynEffect v sig
         , Carrier sig m
         , LambdaValue m :< v
         , BaseValue :< v
         , DynValue :< v
         ) => EvalPrim m v (Const DynPrim) where
  evalPrim = \case
    Const NewVar ->
      pure $ mkVLam @m $ \a ->
      pure $ mkVLam @m $ \f -> do
        Just f' <- pure $ projLambda f
        DynState fresh <- get
        modify (\(DynState x) -> DynState (x + 1))
        f' (mkVDynVar (DVar fresh) a)

    Const NewGlobalVar ->
      pure $ mkVLam @m $ \a -> do
        DynState fresh <- get
        modify (\(DynState x) -> DynState (x + 1))
        pure (mkVDynVar (DVar fresh) a)

    Const AskVar ->
      pure $ mkVLam @m $ \v -> do
        Just (VDynVar x def) <- pure $ projDynVar v
        mx <- asks @(DynEnv v) (lookupEnv x)
        case mx of
          Nothing -> pure def
          Just a -> pure a

    Const SetVar ->
      pure $ mkVLam @m $ \v ->
      pure $ mkVLam @m $ \a ->
      pure $ mkVLam @m $ \f -> do
        Just (VDynVar x _) <- pure $ projDynVar v
        Just f' <- pure $ projLambda f
        local @(DynEnv v) (updateEnv x a) (f' mkVUnit)

instance (DynType :<< t) => TypePrim t (Const DynPrim) where
  typePrim = \case
    Const NewVar ->
      forall Star $ \a ->
      forall Star $ \r ->
      mono $
        let x = TVar 5 Region
        in a ~> typeForall x ((typeParameterOf (Fix (TRef x)) a) ~> r) ~> r

    Const NewGlobalVar ->
      forall Star $ \a ->
      mono $
        a ~> typeParameterOf (typeCtor DTGlobal) a

    Const AskVar ->
      forall Star $ \a ->
      forall Region $ \r ->
      mono $
        typeParameterOf r a ~> a

    Const SetVar ->
      forall Star $ \a ->
      forall Star $ \b ->
      forall Region $ \r ->
      mono $
        typeParameterOf r a ~> a ~> (Fix TUnit ~> b) ~> b

typeForall :: TVar -> Type t -> Type t
typeForall x = Fix . TForall x

typeParameterOf :: (DynType :<< t) => Type t -> Type t -> Type t
typeParameterOf r a = typeCtor DTParameter @: r @: a
