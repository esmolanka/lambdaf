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

module Prim.Anf
  ( AnfEffect
  , AnfEffectC
  , runAnf
  , AnfPrim(..)
  , EPrim(..)
  , AnfValue(..)
  , mkVAnf
  , projAnf
  ) where

import Prelude hiding ((**))

import Control.Effect.Carrier
import Control.Effect.State

import Data.Functor.Const
import Data.Functor.Foldable (Fix (..), unfix)
import qualified Data.Set as S
import Data.Sum
import Data.Text.Prettyprint.Doc as PP

import Eval
import Expr
import Pretty
import Prim.Base
import Types
import Utils

type AnfEffect = State EVar
type AnfEffectC = StateC EVar

runAnf :: (Monad m) => AnfEffectC m a -> m a
runAnf = evalState (EVar 100)

data AnfPrim
  = EConst
  | EPrim EPrim
  | ELoop
  | EReturn
  deriving (Show)

data AnfValue e
  = VAnf EExpr
  | VStore EVar EExpr e
  deriving (Show)

mkVAnf :: (AnfValue :< v) => EExpr -> Value v
mkVAnf = Fix . inject . VAnf

mkVStore :: (AnfValue :< v) => EVar -> EExpr -> Value v -> Value v
mkVStore x s r = Fix (inject (VStore x s r))

projAnf :: (AnfValue :< v) => Value v -> Maybe (AnfValue (Value v))
projAnf = project @AnfValue . unfix

instance Pretty1 AnfValue where
  liftPretty pp = \case
    VAnf e -> align $ ppEExpr e
    VStore x s r -> align $ group $ nest 2 $ vsep
      [ "STORING" <+> ppEVar x <+> ppEExpr s
      , "IN" <+> pp r
      ]

instance PrettyPrim (Const AnfPrim) where
  prettyPrim = \case
    Const EConst -> "EConst"
    Const (EPrim p) -> ppEPrim p
    Const ELoop -> "ELoop"
    Const EReturn -> "EReturn"

instance
  ( Member (RuntimeErrorEffect) sig
  , Member (EnvEffect v) sig
  , Member (AnfEffect) sig
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
          _ -> evalError "Value is not a double!"

    Const (EPrim eprim) ->
      pure $ mkVLam @m $ \x ->
      pure $ mkVLam @m $ \y ->
        case projAnf x of
          Just (VAnf x') ->
            case projAnf y of
              Just (VAnf y') -> do
                anf <- eapply eprim x' y'
                pure (mkVAnf anf)
              _ -> evalError "RHS is not an ANF!"
          _ -> evalError "LHS is not an ANF!"

    Const ELoop ->
      pure $ mkVLam @m $ \f ->
        case projLambda f of
          Just (VLam f') -> do
            stateVar <- fresh
            res <- f' (mkVAnf (EIntro stateVar (EIn (ERef stateVar))))
            let store :: Value v -> m (Value v)
                store v = case (projBase v, projAnf v) of
                  (_, Just (VStore x s r)) -> do
                    r' <- store r
                    case projAnf r' of
                      Just (VAnf r'') -> mkVAnf <$> eapply (EStore x) (EIntro x s) r''
                      _ -> pure (mkVStore x s r')
                  (Just (VPair s r), _) ->
                    case projAnf s of
                      Just (VAnf s') ->
                        case projAnf r of
                          Just (VAnf r') -> mkVAnf <$> eapply (EStore stateVar) (EIntro stateVar s') r'
                          _ -> pure (mkVStore stateVar s' r)
                      _ -> evalError $ "Loop result is not a VStore or VPair"
                  _ -> evalError $ "Loop result is not a VStore or VPair"
            store res
          _ -> evalError "Loop body is not a function!"

    Const EReturn ->
      pure $ mkVLam @m $ \a -> pure a

instance TypePrim (Const AnfPrim) where
  typePrim = \case
    Const EConst ->
      effect $ \e1 ->
      mono $
        (Fix (T TDouble), e1) ~> Fix (TExpr (Fix (TE TEDouble)))

    Const (EPrim EAdd) ->
      effect $ \e1 ->
      effect $ \e2 ->
      mono $
        (Fix (TExpr (Fix (TE TEDouble))), e1) ~>
        (Fix (TExpr (Fix (TE TEDouble))), e2) ~> Fix (TExpr (Fix (TE TEDouble)))

    Const (EPrim (EStore _)) ->
      error "EStore should not apprear in expressions"

    Const ELoop ->
      forall EStar $ \a ->
      forall Star $ \b ->
      effect $ \e1 ->
      mono $
        ((Fix (TExpr a), e1) ~> Fix (TPair (Fix (TExpr a)) b), e1) ~> b

    Const EReturn ->
      forall EStar $ \a ->
      effect $ \e1 ->
      mono $
        (Fix (TExpr a), e1) ~> Fix (TExpr a)

----------------------------------------------------------------------
-- ANF

newtype EVar = EVar Int
  deriving (Show, Eq, Ord)

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
  modify (\(EVar n) -> EVar (succ n))
  return x

eapply :: (Member (State EVar) sig, Carrier sig m) => EPrim -> EExpr -> EExpr -> m EExpr
eapply newprim lhs rhs = do
  var' <- fresh
  pure (go var' S.empty lhs)
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

ppEVar :: EVar -> Doc ann
ppEVar (EVar n) = "@" <> pretty n

ppEValue :: EValue -> Doc ann
ppEValue = \case
  ERef ref -> ppEVar ref
  ELit dbl -> pretty dbl

ppEPrim :: EPrim -> Doc ann
ppEPrim = pretty . show

ppEExpr :: EExpr -> Doc ann
ppEExpr = \case
  ELet ref prim args rest -> vsep
    [ "LET" <+> ppEVar ref <+> "=" <+>
        angles (ppEPrim prim) <+> list (map ppEValue args)
    , ppEExpr rest
    ]
  EIntro ref rest -> vsep
    [ "INTRO" <+> ppEVar ref
    , ppEExpr rest
    ]
  EIn val -> "IN" <+> ppEValue val
