{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveFunctor              #-}
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

module Prim.Kappa
  ( KappaEffect
  , KappaEffectC
  , runKappa
  , KappaPrim(..)
  , EPrim(..)
  , EPrim1(..)
  , KappaValue(..)
  , mkVKappa
  , projKappa
  ) where

import Prelude hiding ((**))

import Control.Effect.Carrier
import Control.Effect.State

import Data.Functor.Const
import Data.Functor.Foldable (Fix (..), unfix)
import Data.Sum
import Data.Text.Prettyprint.Doc as PP

import Eval
import Expr
import Pretty
import Prim.Base
import Types
import Utils

type KappaEffect = State EVar
type KappaEffectC = StateC EVar

runKappa :: (Monad m) => KappaEffectC m a -> m a
runKappa = evalState (EVar 100)

data KappaPrim
  = KConst
  | KVec
  | KComp
  | KPrim EPrim
  | KPrim1 EPrim1
  | KKappa

data KappaValue e
  = VKappa EExpr

mkVKappa :: (KappaValue :< v) => EExpr -> Value v
mkVKappa = Fix . inject . VKappa

projKappa :: (KappaValue :< v) => Value v -> Maybe EExpr
projKappa = fmap (\(VKappa e) -> e) . project @KappaValue . unfix

instance Pretty1 KappaValue where
  liftPretty _pp = \case
    VKappa e -> pretty (show e)

instance PrettyPrim (Const KappaPrim) where
  prettyPrim = \case
    Const KConst     -> "κ/lift"
    Const KVec       -> "κ/vec"
    Const (KPrim p)  -> "κ/" <> angles (pretty (show p))
    Const (KPrim1 p) -> "κ/" <> angles (pretty (show p))
    Const KKappa     -> "κ/abs"
    Const KComp      -> "κ/·"

instance
  ( Member (RuntimeErrorEffect) sig
  , Member KappaEffect sig
  , Carrier sig m
  , LambdaValue m :< v
  , BaseValue :< v
  , KappaValue :< v
  ) => EvalPrim m v (Const KappaPrim) where
  evalPrim = \case
    Const KConst ->
      pure $ mkVLam @m $ \x ->
        case projBase x of
          Just (VDbl x') -> pure $ mkVKappa (EPrim (ELit x'))
          _ -> evalError "Value is not a double!"

    Const KVec ->
      pure $ mkVLam @m $ \xs ->
        case projBase xs of
          Just (VList xs') -> do
            xs'' <- traverse (\x -> case projBase x of {Just (VDbl x') -> pure x'; _ -> evalError "Value is not a double!" }) xs'
            pure $ mkVKappa (EPrim (EVec xs''))
          _ -> evalError "Value is not a list of doubles!"

    Const (KPrim p) ->
      pure $ mkVKappa (EPrim p)

    Const (KPrim1 p) ->
      pure $ mkVLam @m $ \f ->
      case projKappa f of
        Just f' -> pure $ mkVKappa (EPrim1 p f')
        _ -> evalError "Argument is not a kappa!"

    Const KComp ->
      pure $ mkVLam @m $ \f ->
      pure $ mkVLam @m $ \g ->
        case (projKappa f, projKappa g) of
          (Just f', Just g') -> pure $ mkVKappa (EComp f' g')
          _ -> evalError "Argument is not a kappa!"

    Const KKappa ->
      pure $ mkVLam @m $ \f ->
        case projLambda f of
          Just f' -> do
            var <- get
            modify (\(EVar n) -> EVar (n + 1))
            body <- f' (mkVKappa (ERef var))
            case projKappa body of
              Just body' -> pure $ mkVKappa (EKappa var body')
              _ -> evalError "Lambda returned not a kappa!"
          _ -> evalError "Value is not a lambda!"

instance TypePrim (Const KappaPrim) where
  typePrim = \case
    Const KConst ->
      forall EStack $ \t ->
      mono $
        Fix (T TDouble) ~> Fix (TKappa t (Fix (TSCons (Fix (TE TEDouble)) t)))

    Const KVec ->
      forall EStack $ \t ->
      mono $
        typeListOf (Fix (T TDouble)) ~>
        Fix (TKappa t (typeVectorOf (Fix (TE TEDouble)) #: t))

    Const KComp ->
      forall EStack $ \a ->
      forall EStack $ \b ->
      forall EStack $ \c ->
      mono $
        Fix (TKappa a b) ~> Fix (TKappa b c) ~> Fix (TKappa a c)

    Const (KPrim EId) ->
      forall EStack $ \t ->
      mono $
        Fix (TKappa t t)

    Const (KPrim (ELit _)) ->
      forall EStack $ \t ->
      mono $
        Fix (TKappa t (Fix (TE TEDouble) #: t))

    Const (KPrim (EVec _)) ->
      forall EStack $ \t ->
      mono $
        Fix (TKappa t (typeVectorOf (Fix (TE TEDouble)) #: t))

    Const (KPrim EAdd) ->
      forall EStack $ \t ->
      mono $
        Fix (TKappa (Fix (TE TEDouble) #: Fix (TE TEDouble) #: t) (Fix (TE TEDouble) #: t))

    Const (KPrim EMul) ->
      forall EStack $ \t ->
      mono $
        Fix (TKappa (Fix (TE TEDouble) #: Fix (TE TEDouble) #: t) (Fix (TE TEDouble) #: t))

    Const (KPrim ESub) ->
      forall EStack $ \t ->
      mono $
        Fix (TKappa (Fix (TE TEDouble) #: Fix (TE TEDouble) #: t) (Fix (TE TEDouble) #: t))

    Const (KPrim EDiv) ->
      forall EStack $ \t ->
      mono $
        Fix (TKappa (Fix (TE TEDouble) #: Fix (TE TEDouble) #: t) (Fix (TE TEDouble) #: t))

    Const (KPrim1 EFold) ->
      forall EStar $ \a ->
      forall EStack $ \t ->
      mono $
        Fix (TKappa (a #: t) t) ~>
        Fix (TKappa (typeVectorOf a #: t) t)

    Const (KPrim1 ELoop) ->
      forall EStar $ \a ->
      forall EStack $ \t ->
      forall EStack $ \t' ->
      mono $
       Fix (TKappa (Fix (TSCons a t)) (Fix (TSCons a t'))) ~> Fix (TKappa t t')

    Const KKappa ->
      forall EStar $ \a ->
      forall EStack $ \t ->
      forall EStack $ \t' ->
      mono $
        let f = let v = TVar 10 EStack
                    t'' = Fix (TRef v)
                in Fix (TForall v (Fix (TKappa t'' (Fix (TSCons a t''))))) ~> Fix (TKappa t t')
        in f ~> Fix (TKappa (Fix (TSCons a t)) t')

----------------------------------------------------------------------

data EPrim
  = EId
  | ELit Double
  | EVec [Double]
  | EAdd
  | EMul
  | ESub
  | EDiv
  deriving (Show)

data EPrim1
  = EFold
  | ELoop
  deriving (Show)

newtype EVar = EVar Int
  deriving (Show)

data EExpr
  = ERef   EVar
  | EComp  EExpr EExpr
  | EKappa EVar EExpr
  | EPrim  EPrim
  | EPrim1 EPrim1 EExpr
    deriving (Show)
