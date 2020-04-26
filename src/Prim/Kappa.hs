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
  , KappaValue(..)
  , mkVVal
  , mkVAbs
  , projVal
  , projAbs
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

type KappaEffect = State EState
type KappaEffectC = StateC EState

runKappa :: (Monad m) => KappaEffectC m a -> m a
runKappa = evalState (EState (EVar 100) id [])

data KappaPrim
  = KConstDbl
  | KConstVec
  | KConstNil
  | KPrim EPrim
  | KAbs

data KappaValue e
  = VVal EValue
  | VAbs EAbs

mkVVal :: (KappaValue :< v) => EValue -> Value v
mkVVal = Fix . inject . VVal

mkVAbs :: (KappaValue :< v) => [EVar] -> EExpr -> Value v
mkVAbs = ((Fix . inject . VAbs) .) . EAbs

projVal :: (KappaValue :< v) => Value v -> Maybe EValue
projVal v = case project @KappaValue (unfix v) of
  Just (VVal e) -> Just e
  _ -> Nothing

projAbs :: (KappaValue :< v) => Value v -> Maybe EAbs
projAbs v = case project @KappaValue (unfix v) of
  Just (VAbs f) -> Just f
  _ -> Nothing

instance Pretty1 KappaValue where
  liftPretty _pp = \case
    VVal v -> ppEValue v
    VAbs f  -> ppEAbs f

instance PrettyPrim (Const KappaPrim) where
  prettyPrim = \case
    Const KConstDbl  -> "κ/▴"
    Const KConstVec  -> "κ/▴ⁿ"
    Const KConstNil  -> "κ/∅"
    Const (KPrim p)  -> "κ/" <> pretty (show p)
    Const KAbs       -> "κ"

instance
  ( Member RuntimeErrorEffect sig
  , Member KappaEffect sig
  , Carrier sig m
  , LambdaValue m :< v
  , BaseValue :< v
  , KappaValue :< v
  ) => EvalPrim m v (Const KappaPrim) where
  evalPrim = \case
    Const KConstDbl ->
      pure $ mkVLam @m $ \x ->
        case projBase x of
          Just (VDbl x') -> pure $ mkVVal (ELit x')
          _ -> evalError "Value is not a double!"

    Const KConstVec ->
      pure $ mkVLam @m $ \xs ->
        case projBase xs of
          Just (VList xs') -> do
            xs'' <- traverse (\x -> case projBase x of {Just (VDbl x') -> pure x'; _ -> evalError "Value is not a double!" }) xs'
            pure $ mkVVal (EVec xs'')
          _ -> evalError "Value is not a list of doubles!"

    Const KConstNil ->
      pure $ mkVVal ENil

    Const (KPrim EFold) ->
      pure $ mkVLam @m $ \f ->
      pure $ mkVLam @m $ \x ->
      pure $ mkVLam @m $ \y ->
        case (projAbs f, projVal x, projVal y) of
          (Just f', Just x', Just y') -> mkVVal <$> eapply EFold [f'] [x', y']
          _ -> evalError "Wrong argument"

    Const (KPrim ELoop) ->
      pure $ mkVLam @m $ \f ->
        case projAbs f of
          Just f' -> mkVVal <$> eapply ELoop [f'] []
          _ -> evalError "Wrong argument"

    Const (KPrim EHead) ->
      pure $ mkVLam @m $ \x ->
        case projVal x of
          Just x' -> mkVVal <$> eapply EHead [] [x']
          _ -> evalError "Wrong argument"

    Const (KPrim ETail) ->
      pure $ mkVLam @m $ \x ->
        case projVal x of
          Just x' -> mkVVal <$> eapply ETail [] [x']
          _ -> evalError "Wrong argument"

    Const (KPrim prim) ->
      pure $ mkVLam @m $ \x ->
      pure $ mkVLam @m $ \y ->
        case (projVal x, projVal y) of
          (Just x', Just y') -> mkVVal <$> eapply prim [] [x', y']
          _ -> evalError "Wrong argument"

    Const KAbs ->
      pure $ mkVLam @m $ \f ->
        case projLambda f of
          Just f' -> do
            ekappa $ \var -> do
              res <- f' (mkVVal (ERef var))
              case (projVal res, projAbs res) of
                (Just res', _) -> do
                  body <- ereturn res'
                  pure $ mkVAbs [var] body
                (_, Just (EAbs vars body')) -> pure $ mkVAbs (var : vars) body'
                _ -> evalError "Lambda returned not a kappa!"
          _ -> evalError "Value is not a lambda!"

instance TypePrim (Const KappaPrim) where
  typePrim = \case
    Const KConstDbl ->
      mono $
        Fix (T TDouble) ~>
        typeExprOf (Fix (TCtor "EDouble"))

    Const KConstVec ->
      mono $
        typeListOf (Fix (T TDouble)) ~>
        typeExprOf (typeVectorOf (Fix (TCtor "EDouble")))

    Const KConstNil ->
      mono $
        typeExprOf (typeTupleOf (Fix TSNil))

    Const (KPrim EAdd) ->
      mono $
        typeExprOf (Fix (TCtor "EDouble")) ~>
        typeExprOf (Fix (TCtor "EDouble")) ~>
        typeExprOf (Fix (TCtor "EDouble"))

    Const (KPrim EMul) ->
      mono $
        typeExprOf (Fix (TCtor "EDouble")) ~>
        typeExprOf (Fix (TCtor "EDouble")) ~>
        typeExprOf (Fix (TCtor "EDouble"))

    Const (KPrim ESub) ->
      mono $
        typeExprOf (Fix (TCtor "EDouble")) ~>
        typeExprOf (Fix (TCtor "EDouble")) ~>
        typeExprOf (Fix (TCtor "EDouble"))

    Const (KPrim EDiv) ->
      mono $
        typeExprOf (Fix (TCtor "EDouble")) ~>
        typeExprOf (Fix (TCtor "EDouble")) ~>
        typeExprOf (Fix (TCtor "EDouble"))

    Const (KPrim ECons) ->
      forall EStar $ \a ->
      forall EStack $ \t ->
      mono $
        typeExprOf a ~>
        typeExprOf (typeTupleOf t) ~>
        typeExprOf (typeTupleOf (a #: t))

    Const (KPrim EHead) ->
      forall EStar $ \a ->
      forall EStack $ \t ->
      mono $
        typeExprOf (typeTupleOf (a #: t)) ~>
        typeExprOf a

    Const (KPrim ETail) ->
      forall EStar $ \a ->
      forall EStack $ \t ->
      mono $
        typeExprOf (typeTupleOf (a #: t)) ~>
        typeExprOf (typeTupleOf t)

    Const (KPrim EFold) ->
      forall EStar $ \a ->
      forall EStar $ \b ->
      mono $
        Fix (TEArrow (a #: b #: Fix TSNil) b) ~>
        typeExprOf b ~>
        typeExprOf (typeVectorOf a) ~>
        typeExprOf b

    Const (KPrim ELoop) ->
      forall EStar  $ \a ->
      forall EStack $ \t ->
      forall EStack $ \t' ->
      mono $
        Fix (TEArrow (a #: t) (typeTupleOf (a #: t'))) ~>
        Fix (TEArrow t (typeTupleOf t'))

    Const KAbs ->
      forall EStar $ \a ->
      forall EStar $ \b ->
      forall EStack $ \t ->
      mono $
        (Fix (TEArrow (Fix TSNil) a) ~> Fix (TEArrow t b)) ~> Fix (TEArrow (a #: t) b)

----------------------------------------------------------------------

data EState = EState
  { freshVar :: EVar
  , focused  :: EExpr -> EExpr
  , unfocused :: [EExpr -> EExpr]
  }

newtype EVar = EVar Int
  deriving (Show, Ord, Eq)

data EPrim
  = EAdd
  | EMul
  | ESub
  | EDiv
  | ECons
  | EHead
  | ETail
  | EFold
  | ELoop
  deriving (Show, Eq, Ord)

data EExpr
  = EReturn EValue
  | ELet EVar EPrim [EAbs] [EValue] EExpr
  deriving (Show)

data EAbs = EAbs [EVar] EExpr
  deriving (Show)

data EValue
  = ERef EVar
  | EUnit
  | ELit Double
  | EVec [Double]
  | ENil
  deriving (Show)

fresh :: (Member KappaEffect sig, Carrier sig m) => m EVar
fresh = do
  x <- gets freshVar
  modify (\st -> let EVar n = freshVar st in st { freshVar = EVar (succ n) })
  return x

ekappa :: (Member KappaEffect sig, Carrier sig m) => (EVar -> m a) -> m a
ekappa body = do
  modify $ \st -> st
    { focused   = id
    , unfocused = focused st : unfocused st
    }
  var <- fresh
  body var


eapply :: (Member KappaEffect sig, Carrier sig m) => EPrim -> [EAbs] -> [EValue] -> m EValue
eapply p fs xs = do
  var <- fresh
  let entry = ELet var p fs xs
  modify $ \st -> st { focused = focused st . entry }
  pure (ERef var)

ereturn :: (Member KappaEffect sig, Carrier sig m) => EValue -> m EExpr
ereturn result = do
  expr <- gets focused
  rest <- gets unfocused
  case rest of
    [] -> modify $ \st -> st { focused = id }
    (c : cs) -> modify $ \st -> st { focused = c, unfocused = cs }
  pure $ expr $ EReturn result

----------------------------------------------------------------------

ppEVar :: EVar -> Doc ann
ppEVar (EVar n) = "@" <> pretty n

ppEValue :: EValue -> Doc ann
ppEValue = \case
  ERef ref -> ppEVar ref
  EUnit    -> "Unit"
  ELit dbl -> pretty dbl
  EVec vec -> pretty vec
  ENil     -> "Nil"

ppEPrim :: EPrim -> Doc ann
ppEPrim = pretty . show

ppEAbs :: EAbs -> Doc ann
ppEAbs (EAbs vars body) =
  vsep [ hsep ("κ" : punctuate comma (map ppEVar vars)) <> "."
       , indent 2 $ ppEExpr body
       ]

ppEExpr :: EExpr -> Doc ann
ppEExpr = \case
  ELet ref prim fs args rest -> vsep $
    [ "LET" <+> ppEVar ref <+> "=" <+> ppEPrim prim <+> tupled (map ppEValue args) ] ++
    map (\fun -> indent 2 $ "WITH" <+> ppEAbs fun) fs ++
    [ ppEExpr rest ]
  EReturn val ->
    "RETURN" <+> ppEValue val
