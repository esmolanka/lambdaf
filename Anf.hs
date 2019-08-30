{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveFunctor              #-}
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

module Anf where

import Prelude hiding ((**))

import Control.Effect.Carrier
import Control.Effect.Error
import Control.Effect.Reader
import Control.Effect.State

import Data.Functor.Classes
import Data.Functor.Const
import Data.Functor.Foldable (Fix (..), unfix)
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Sum

import Expr
import Base (BaseValue(..))
import Utils

data AnfValue e
  = VAnf EExpr
  | VStore EVar EExpr e
  deriving (Show)

mkVAnf :: (AnfValue :< v) => EExpr -> Value v
mkVAnf = Fix . inject . VAnf

mkVStore :: (AnfValue :< v) => EVar -> EExpr -> Value v -> Value v
mkVStore x s r = Fix (inject (VStore x s r))

instance Show1 AnfValue where
  liftShowsPrec sp _ _ = \case
    VAnf e -> showString "{" . shows e . showString "}"
    VStore x s r -> showString "{@" . shows x . showString " = " . shows s . showString "; " . sp 0 r . showString "}"

data AnfPrim
  = EConst
  | EPrim EPrim
  | ELoop
  deriving (Show)

instance
  ( Member (Error String) sig
  , Member (Reader (M.Map Var (Value v))) sig
  , Member (State EVar) sig
  , Carrier sig m
  , LambdaValue m :< v
  , BaseValue :< v
  , AnfValue :< v
  ) => EvalPrim m v (Const AnfPrim) where
  evalPrim = \case
    Const EConst ->
      pure $ mkVLam @m $ \x ->
        case projBase x of
          Just (VDbl x') -> pure $ mkVAnf (EIn (ELit x'))
          _ -> throwError "Value is not a double!"

    Const (EPrim eprim) ->
      pure $ mkVLam @m $ \x ->
      pure $ mkVLam @m $ \y ->
        case projAnf x of
          Just (VAnf x') ->
            case projAnf y of
              Just (VAnf y') -> do
                anf <- eapply eprim x' y'
                pure (mkVAnf anf)
              _ -> throwError "RHS is not an ANF!"
          _ -> throwError "LHS is not an ANF!"

    Const ELoop ->
      pure $ mkVLam @m $ \f ->
        case projLam f of
          Just (VLam f') -> do
            stateVar <- fresh
            res <- f' (mkVAnf (EIntro stateVar (EIn (ERef stateVar))))
            let store :: Value v -> m (Value v)
                store v = case (projBase v, projAnf v) of
                  (_, Just (VStore x s r))  -> mkVStore x s <$> store r
                  (Just (VPair s r), _) ->
                    case projAnf s of
                      (Just (VAnf s')) -> pure (mkVStore stateVar s' r)
                      _                -> throwError $ "Loop result is not a VStore or VPair"
                  _               -> throwError $ "Loop result is not a VStore or VPair"

                flatten :: Value v -> m EExpr
                flatten v = case projAnf v of
                  Just (VStore x s r) -> eapply (EStore x) (EIntro x s) =<< flatten r
                  Just (VAnf x)       -> pure x
                  _                   -> throwError "Can't flatten yet"

            (store res >>= flatten >>= pure . mkVAnf) `catchError` (\(_ :: String) -> store res)

          _ -> throwError "Loop body is not a function!"
    where
      projLam :: (LambdaValue m :< v) => Value v -> Maybe (LambdaValue m (Value v))
      projLam = project @(LambdaValue m) . unfix

      projBase :: (BaseValue :< v) => Value v -> Maybe (BaseValue (Value v))
      projBase = project @BaseValue . unfix

      projAnf :: (AnfValue :< v) => Value v -> Maybe (AnfValue (Value v))
      projAnf = project @AnfValue . unfix

----------------------------------------------------------------------
-- ANF

type EVar = Int

data EPrim = EAdd | EStore EVar
  deriving (Show)

data EExpr
  = ELet   EVar EPrim [EValue] EExpr
  | EIntro EVar EExpr
  | EIn    EValue
    deriving (Show)

data EValue
  = ERef EVar
  | ELit Double
    deriving (Show)

fresh :: (Member (State EVar) sig, Carrier sig m) => m EVar
fresh = do
  x <- get
  modify (succ :: EVar -> EVar)
  return x

eapply :: (Member (State EVar) sig, Carrier sig m) => EPrim -> EExpr -> EExpr -> m EExpr
eapply newprim lhs rhs = do
  var <- fresh
  pure (go var S.empty lhs)
  where
    go :: EVar -> S.Set EVar -> EExpr -> EExpr
    go x used = \case
      ELet ref prim args rest
        | S.member ref used -> go x used rest
        | otherwise -> ELet ref prim args (go x (S.insert ref used) rest)
      EIntro ref rest
        | S.member ref used -> go x used rest
        | otherwise -> EIntro ref (go x (S.insert ref used) rest)
      EIn lhsval ->
        go2 lhsval x used rhs

    go2 :: EValue -> EVar -> S.Set EVar -> EExpr -> EExpr
    go2 lhsval x used = \case
      ELet ref prim args rest
        | S.member ref used  -> go2 lhsval x used rest
        | otherwise -> ELet ref prim args (go2 lhsval x (S.insert ref used) rest)
      EIntro ref rest
        | S.member ref used  -> go2 lhsval x used rest
        | otherwise -> EIntro ref (go2 lhsval x (S.insert ref used) rest)
      EIn rhsval ->
        ELet x newprim [lhsval, rhsval] (EIn (ERef x))

----------------------------------------------------------------------

cnst :: (AnfPrim :<< p) => Expr p -> Expr p
cnst x = Fix (Prim (inject' EConst)) ! x

eadd :: (AnfPrim :<< p) => Expr p -> Expr p -> Expr p
eadd x y = Fix (Prim (inject' (EPrim EAdd))) ! x ! y

loop :: (AnfPrim :<< p) => Expr p -> Expr p
loop x = Fix (Prim (inject' ELoop)) ! x
