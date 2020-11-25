{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RecordWildCards            #-}
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
  , KappaValue(..)
  , mkVVal
  , mkVAbs
  , projVal
  , projAbs
  , toEExpr
  , KappaType(..)
  , typeVectorOf
  ) where

import Prelude hiding ((**))

import Control.Algebra
import Control.Effect.State
import Control.Carrier.State.Strict
import Control.Monad

import Data.Fix (Fix (..))
import Data.Functor.Const
import Data.Sum
import Data.Text.Prettyprint.Doc as PP

import Eval
import Expr
import Pretty
import Prim.Base
import Types
import Utils

type KappaEffect = State EState
type KappaEffectC = StateC EState

runKappa :: (Monad m) => KappaEffectC m a -> m a
runKappa = evalState (EState (EVar 100) id [])

data KappaPrim
  = KConstDbl
  | KConstVec
  | KConstBool
  | KPrim EPrim
  | KLoop

data KappaType
  = KTBool
  | KTFloat
  | KTVector
  | KTDyn
    deriving (Eq, Show)

instance PrettyType (Const KappaType) where
  prettySpine _lvl = \case
    (Const KTVector, [a]) -> Just $ a 2 <> "[]"
    (Const KTDyn, [a]) -> Just $ "Dyn⟨" <> a 0 <> "⟩"
    _ -> Nothing

  prettyCtor = \case
    Const KTBool   -> "Bool"
    Const KTFloat  -> "Float"
    Const KTVector -> "Vector"
    Const KTDyn    -> "Dyn"

instance KindOfCtor (Const KappaType) where
  kindOfCtor = \case
    Const KTBool   -> EStar
    Const KTFloat  -> EStar
    Const KTVector -> EStar `Arr` EStar
    Const KTDyn    -> EStar `Arr` Star

typeVectorOf :: (KappaType :<< t) => Type t -> Type t
typeVectorOf a = typeCtor KTVector @: a

typeDynOf :: (KappaType :<< t) => Type t -> Type t
typeDynOf a = typeCtor KTDyn @: a

data KappaValue e
  = VVal EValue
  | VAbs EAbs

mkVVal :: (KappaValue :< v) => EValue -> Value v
mkVVal = Fix . inject . VVal

mkVAbs :: (KappaValue :< v) => [EVar] -> EExpr -> Value v
mkVAbs = ((Fix . inject . VAbs) .) . EAbs

projVal :: (KappaValue :< v) => Value v -> Maybe EValue
projVal v = case project @KappaValue (unFix v) of
  Just (VVal e) -> Just e
  _ -> Nothing

projAbs :: (KappaValue :< v) => Value v -> Maybe EAbs
projAbs v = case project @KappaValue (unFix v) of
  Just (VAbs f) -> Just f
  _ -> Nothing

instance Pretty1 KappaValue where
  liftPretty _ = \case
    VVal v -> braces (ppEValue v)
    VAbs f -> ppEAbs f

instance Pretty KappaPrim where
  pretty = \case
    KConstDbl  -> "κ/▴"
    KConstVec  -> "κ/▴ⁿ"
    KConstBool -> "κ/▴"
    KPrim p    -> "κ/" <> pretty (show p)
    KLoop      -> "κ/ℓ"

instance
  ( MonadFail m
  , Has RuntimeErrorEffect sig m
  , Has KappaEffect sig m
  , LambdaValue m :< v
  , BaseValue :< v
  , KappaValue :< v
  ) => EvalPrim m v (Const KappaPrim) where
  evalPrim = \case
    Const KConstBool ->
      pure $ mkVLam @m $ \x -> do
        Just (VBool x') <- pure $ projBase x
        pure $ mkVVal (EBool x')

    Const KConstDbl ->
      pure $ mkVLam @m $ \x -> do
        Just (VFloat x') <- pure $ projBase x
        pure $ mkVVal (ELit x')

    Const KConstVec ->
      pure $ mkVLam @m $ \xs -> do
        Just (VList xs') <- pure $ projBase xs
        xs'' <- forM xs' $ \x -> do
          Just (VFloat x') <- pure (projBase x)
          pure x'
        pure $ mkVVal (EVec xs'')

    Const (KPrim EMap) ->
      pure $ mkVLam @m $ \f ->
      pure $ mkVLam @m $ \v -> do
        Just f' <- projAbs <$> mkKappa 1 f
        Just v' <- pure $ projVal v
        mkVVal <$> eapply EMap [f'] [v']

    Const (KPrim EFold) ->
      pure $ mkVLam @m $ \f ->
      pure $ mkVLam @m $ \b ->
      pure $ mkVLam @m $ \xs -> do
        Just xs' <- pure $ projVal xs
        Just b'  <- pure $ projVal b
        Just f' <- pure . projAbs =<< mkKappa 2 f
        mkVVal <$> eapply EFold [f'] [b', xs']

    Const (KPrim EBranch) ->
      pure $ mkVLam @m $ \c ->
      pure $ mkVLam @m $ \t ->
      pure $ mkVLam @m $ \f -> do
        c' <- maybe (evalError "EBranch: c") pure $ projVal c
        t' <- maybe (evalError "EBranch: c") pure $ projVal t
        f' <- maybe (evalError "EBranch: c") pure $ projVal f
        mkVVal <$> eapply EBranch [] [c', t', f']

    Const (KPrim prim) ->
      pure $ mkVLam @m $ \x ->
      pure $ mkVLam @m $ \y -> do
        Just x' <- pure $ projVal x
        Just y' <- pure $ projVal y
        mkVVal <$> eapply prim [] [x', y']

    Const KLoop ->
      pure $ mkVLam @m $ \f -> do
        Just f' <- pure $ projLambda @m f
        eloop $ \x -> do
          Just (VPair v r) <- projBase <$> f' (mkVVal (ERef x))
          Just v' <- pure $ projVal v
          pure (v', r)

mkKappa
  :: forall v sig m.
     ( Has RuntimeErrorEffect sig m
     , Has KappaEffect sig m
     , LambdaValue m :< v
     , KappaValue :< v
     )
  => Int -> Value v -> m (Value v)
mkKappa = go id []
  where
    go :: (EExpr -> EExpr) -> [EVar] -> Int -> Value v -> m (Value v)
    go prefix vars 0 val = do
      val' <- maybe (evalError "A value expected") pure $ projVal val
      pure $ mkVAbs (reverse vars) (prefix $ EReturn val')
    go prefix vars n val = do
      val' <- maybe (evalError "A lambda expected") pure $ projLambda val
      ekappa $ \newvar -> do
        res <- val' (mkVVal (ERef newvar))
        prefix' <- eunkappa
        go (prefix . prefix') (newvar : vars) (n - 1) res

instance (BaseType :<< t, KappaType :<< t) => TypePrim t (Const KappaPrim) where
  typePrim = \case
    Const KConstBool ->
      mono $
        typeCtor BTBool ~>
        (typeDynOf $ typeCtor KTBool)

    Const KConstDbl ->
      mono $
        typeCtor BTFloat ~>
        (typeDynOf $ typeCtor KTFloat)

    Const KConstVec ->
      mono $
        typeListOf (typeCtor BTFloat) ~>
        (typeDynOf $ typeVectorOf (typeCtor KTFloat))

    Const (KPrim EAdd) ->
      mono $
        (typeDynOf $ typeCtor KTFloat) ~>
        (typeDynOf $ typeCtor KTFloat) ~>
        (typeDynOf $ typeCtor KTFloat)

    Const (KPrim EMul) ->
      mono $
        (typeDynOf $ typeCtor KTFloat) ~>
        (typeDynOf $ typeCtor KTFloat) ~>
        (typeDynOf $ typeCtor KTFloat)

    Const (KPrim ESub) ->
      mono $
        (typeDynOf $ typeCtor KTFloat) ~>
        (typeDynOf $ typeCtor KTFloat) ~>
        (typeDynOf $ typeCtor KTFloat)

    Const (KPrim EDiv) ->
      mono $
        (typeDynOf $ typeCtor KTFloat) ~>
        (typeDynOf $ typeCtor KTFloat) ~>
        (typeDynOf $ typeCtor KTFloat)

    Const (KPrim EMap) ->
      forall EStar $ \a ->
      forall EStar $ \b ->
      mono $
        (typeDynOf a ~> typeDynOf b) ~>
        (typeDynOf $ typeVectorOf a) ~>
        (typeDynOf $ typeVectorOf b)

    Const (KPrim EFold) ->
      forall EStar $ \a ->
      forall EStar $ \b ->
      mono $
        (typeDynOf a ~> typeDynOf b ~> typeDynOf b) ~>
        (typeDynOf $ b) ~>
        (typeDynOf $ typeVectorOf a) ~>
        (typeDynOf $ b)

    Const (KPrim EBranch) ->
      forall EStar  $ \a ->
      mono $
        (typeDynOf $ typeCtor KTBool) ~>
        (typeDynOf $ a) ~>
        (typeDynOf $ a) ~>
        (typeDynOf $ a)

    Const KLoop ->
      forall EStar $ \a ->
      forall Star  $ \b ->
      mono $
        (typeDynOf a ~> typePairOf (typeDynOf a) b) ~>
        b


----------------------------------------------------------------------

data EState = EState
  { freshVar :: EVar
  , focused  :: EExpr -> EExpr
  , unfocused :: [EExpr -> EExpr]
  }

newtype EVar = EVar Int
  deriving (Show, Ord, Eq)

newtype EPersistent = EPersistent Int
  deriving (Show, Ord, Eq)

data EPrim
  = EAdd
  | EMul
  | ESub
  | EDiv
  | EFold
  | EMap
  | EBranch
  deriving (Show, Eq, Ord)

data EExpr
  = ELet    EVar EPrim [EAbs] [EValue] EExpr
  | ELoad   EVar EPersistent EExpr
  | EStore  EPersistent EValue EExpr
  | EReturn EValue
  deriving (Show)

data EAbs = EAbs [EVar] EExpr
  deriving (Show)

data EValue
  = ERef  EVar
  | EUnit
  | EBool Bool
  | ELit  Double
  | EVec  [Double]
  deriving (Show)

fresh :: (Has KappaEffect sig m) => m EVar
fresh = do
  x <- gets freshVar
  modify (\st -> let EVar n = freshVar st in st { freshVar = EVar (succ n) })
  return x

ekappa :: (Has KappaEffect sig m) => (EVar -> m a) -> m a
ekappa body = do
  modify $ \st -> st
    { focused   = id
    , unfocused = focused st : unfocused st
    }
  var <- fresh
  -- traceState $ "EKAPPA"
  body var

eapply :: (Has KappaEffect sig m) => EPrim -> [EAbs] -> [EValue] -> m EValue
eapply p fs xs = do
  var <- fresh
  let entry = ELet var p fs xs
  modify $ \st -> st { focused = focused st . entry }
  -- traceState $ "EAPPLY " ++ show p ++ " " ++ show xs ++ " " ++ show fs
  pure (ERef var)

eloop :: (Has KappaEffect sig m) => (EVar -> m (EValue, a)) -> m a
eloop f = do
  EVar n <- fresh
  let eload = ELoad (EVar n) (EPersistent n)
  modify $ \st -> st { focused = focused st . eload }
  (val, res) <- f (EVar n)
  let estore v = EStore (EPersistent n) v
  modify $ \st -> st { focused = focused st . estore val }
  pure res

eunkappa :: (Has RuntimeErrorEffect sig m, Has KappaEffect sig m) => m (EExpr -> EExpr)
eunkappa = do
  expr <- gets focused
  rest <- gets unfocused
  case rest of
    [] -> evalError "eunkappa: can't pop stack anymore"
    (c : cs) -> modify $ \st -> st { focused = c, unfocused = cs }
  pure expr

toEExpr :: (Has RuntimeErrorEffect sig m, Has KappaEffect sig m) => EValue -> m EExpr
toEExpr value = do
  expr <- gets focused
  pure $ expr (EReturn value)

----------------------------------------------------------------------

ppEVar :: EVar -> Doc ann
ppEVar (EVar n) = "@" <> pretty n

ppEPersistent :: EPersistent -> Doc ann
ppEPersistent (EPersistent n) = "State" <> angles (pretty n)

ppEValue :: EValue -> Doc ann
ppEValue = \case
  ERef ref -> ppEVar ref
  EUnit    -> "Unit"
  ELit dbl -> pretty dbl
  EBool b  -> pretty b
  EVec vec -> pretty vec

ppEPrim :: EPrim -> Doc ann
ppEPrim = pretty . show

ppEAbs :: EAbs -> Doc ann
ppEAbs (EAbs vars body) =
  vsep [ ppTuple (map ppEVar vars) <+> "⇒"
       , indent 2 $ ppEExpr body
       ]

ppTuple :: [Doc ann] -> Doc ann
ppTuple [] = "∅"
ppTuple [x] = x
ppTuple xs = tupled xs

ppEExpr :: EExpr -> Doc ann
ppEExpr = \case
  ELet ref prim fs args rest -> vsep $
    [ "LET" <+> ppEVar ref <+> ":=" <+> ppEPrim prim <+> ppTuple (map ppEValue args) ] ++
    map (\fun -> indent 2 $ "WITH" <+> ppEAbs fun) fs ++
    [ ppEExpr rest ]
  ELoad ref persistent rest -> vsep $
    [ "GET" <+> ppEVar ref <+> ":=" <+> ppEPersistent persistent
    , ppEExpr rest
    ]
  EStore persistent ref rest -> vsep $
    [ "SET" <+> ppEPersistent persistent <+> ":=" <+> ppEValue ref
    , ppEExpr rest
    ]
  EReturn val ->
    "RET" <+> ppEValue val

_ppEState :: EState -> Doc ann
_ppEState EState{..} =
  vsep
    ( zipWith ppFrame [0..] (focused : unfocused) ++
      ["======================================================================"
      , mempty
      ]
    )
  where
    ppFrame :: Int -> (EExpr -> EExpr) -> Doc ann
    ppFrame n e = vsep
      [ "Frame" <+> pretty n
      , indent 4 (ppEExpr (e (EReturn EUnit)))
      , "----------------------------------------------------------------------"
      ]
