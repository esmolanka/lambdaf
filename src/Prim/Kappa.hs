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

import Control.Effect.Carrier
import Control.Effect.State
import Control.Monad

import Data.Functor.Const
import Data.Functor.Foldable (Fix (..), unfix)
import Data.Sum
import Data.Text.Prettyprint.Doc as PP

import Eval
import Expr
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
  | KCons
  | KFirst
  | KRest

data KappaType
  = KTBool
  | KTFloat
  | KTVector
  | KTDyn
    deriving (Eq, Show)

instance Pretty KappaType where
  pretty = \case
    KTBool -> "Bool"
    KTFloat -> "Float"
    KTVector -> "Vector"
    KTDyn -> "Dyn"

instance KindOfCtor (Const KappaType) where
  kindOfCtor = \case
    Const KTBool   -> EStar
    Const KTFloat  -> EStar
    Const KTVector -> EStar `Arr` EStar
    Const KTDyn    -> EStack `Arr` Star

typeVectorOf :: (KappaType :<< t) => Type t -> Type t
typeVectorOf a = typeCtor KTVector @: a

typeDynOf :: (KappaType :<< t) => Type t -> Type t
typeDynOf a = typeCtor KTDyn @: a


data KappaValue e
  = VVal [EValue]
  | VAbs EAbs

mkVVal :: (KappaValue :< v) => [EValue] -> Value v
mkVVal = Fix . inject . VVal

mkVAbs :: (KappaValue :< v) => [EVar] -> EExpr -> Value v
mkVAbs = ((Fix . inject . VAbs) .) . EAbs

projVal :: (KappaValue :< v) => Value v -> Maybe [EValue]
projVal v = case project @KappaValue (unfix v) of
  Just (VVal e) -> Just e
  _ -> Nothing

projAbs :: (KappaValue :< v) => Value v -> Maybe EAbs
projAbs v = case project @KappaValue (unfix v) of
  Just (VAbs f) -> Just f
  _ -> Nothing

instance Pretty1 KappaValue where
  liftPretty _ = \case
    VVal v -> braces (hsep (punctuate comma (map ppEValue v)))
    VAbs f -> ppEAbs f

instance Pretty KappaPrim where
  pretty = \case
    KConstDbl  -> "κ/▴"
    KConstVec  -> "κ/▴ⁿ"
    KConstBool -> "κ/▴"
    (KPrim p)  -> "κ/" <> pretty (show p)
    KCons      -> "κ/**"
    KFirst     -> "κ/!"
    KRest      -> "κ/…"

instance
  ( Member RuntimeErrorEffect sig
  , Member KappaEffect sig
  , Carrier sig m
  , LambdaValue m :< v
  , BaseValue :< v
  , KappaValue :< v
  ) => EvalPrim m v (Const KappaPrim) where
  evalPrim = \case
    Const KConstBool ->
      pure $ mkVLam @m $ \x ->
        case projBase x of
          Just (VBool x') -> pure $ mkVVal [EBool x']
          _ -> evalError "Value is not a bool!"

    Const KConstDbl ->
      pure $ mkVLam @m $ \x ->
        case projBase x of
          Just (VFloat x') -> pure $ mkVVal [ELit x']
          _ -> evalError "Value is not a double!"

    Const KConstVec ->
      pure $ mkVLam @m $ \xs ->
        case projBase xs of
          Just (VList xs') -> do
            xs'' <- traverse (\x -> case projBase x of {Just (VFloat x') -> pure x'; _ -> evalError "Value is not a double!" }) xs'
            pure $ mkVVal [EVec xs'']
          _ -> evalError "Value is not a list of doubles!"

    Const (KPrim EMap) ->
      pure $ mkVLam @m $ \f ->
      pure $ mkVLam @m $ \v -> do
        f' <- maybe (evalError "EMap: f") pure . projAbs =<< mkKappa [1] f
        v' <- maybe (evalError "EMap: v") pure $ projVal v
        mkVVal <$> eapply EMap 1 [f'] v'

    Const (KPrim EFold) ->
      pure $ mkVLam @m $ \f ->
      pure $ mkVLam @m $ \xs ->
      pure $ mkVLam @m $ \b -> do
        xs' <- maybe (evalError "EFold: xs") pure $ projVal xs
        b' <- maybe (evalError "EFold: v") pure $ projVal b
        let n = length b'
        f' <- maybe (evalError "EFold: f") pure . projAbs =<< mkKappa [1, n] f
        mkVVal <$> eapply EFold n [f'] (head xs' : b')

    Const (KPrim ELoop) ->
      pure $ mkVLam @m $ \f -> do
        f' <- maybe (evalError "ELoop: f") pure . projAbs =<< mkKappa [1] f
        let coarity = go f' - 1
              where
                go (EAbs _ expr) = go' expr
                go' (ELet _ _ _ _ k) = go' k
                go' (EReturn xs) = length xs
        mkVVal <$> eapply ELoop coarity [f'] []

    Const (KPrim EBranch) ->
      pure $ mkVLam @m $ \c ->
      pure $ mkVLam @m $ \t ->
      pure $ mkVLam @m $ \f ->
        case (projVal c, projVal t, projVal f) of
          (Just [c'], Just [t'], Just [f']) -> mkVVal <$> eapply EBranch 1 [] [c', t', f']
          _ -> evalError "Wrong argument"

    Const (KPrim prim) ->
      pure $ mkVLam @m $ \x ->
      pure $ mkVLam @m $ \y ->
        case (projVal x, projVal y) of
          (Just [x'], Just [y']) -> mkVVal <$> eapply prim 1 [] [x', y']
          _ -> evalError "Wrong argument"

    Const KCons ->
      pure $ mkVLam @m $ \h ->
      pure $ mkVLam @m $ \t ->
        case (projVal h, projVal t) of
          (Just [h'], Just t') -> pure (mkVVal (h' : t'))
          other -> evalError $ "ECons: wrong arguments: " ++ show other

    Const KFirst ->
      pure $ mkVLam @m $ \x ->
        case projVal x of
          Just (x' : _) -> pure $ mkVVal [x']
          other -> evalError $ "Not a value: " ++ show other

    Const KRest ->
      pure $ mkVLam @m $ \x ->
        case projVal x of
          Just (_ : xs) -> pure $ mkVVal xs
          other -> evalError $ "Not a value: " ++ show other

mkKappa
  :: forall v sig m.
     ( Member RuntimeErrorEffect sig
     , Member KappaEffect sig
     , Carrier sig m
     , LambdaValue m :< v
     , KappaValue :< v
     )
  => [Int] -> Value v -> m (Value v)
mkKappa = go id []
  where
    go :: (EExpr -> EExpr) -> [EVar] -> [Int] -> Value v -> m (Value v)
    go prefix vars [] val = do
      val' <- maybe (evalError "A value expected") pure $ projVal val
      pure $ mkVAbs (reverse vars) (prefix $ EReturn val')
    go prefix vars (arity : rest) val = do
      val' <- maybe (evalError "A lambda expected") pure $ projLambda val
      ekappa arity $ \newvars -> do
        res <- val' (mkVVal (map ERef newvars))
        prefix' <- eunkappa
        go (prefix . prefix') (reverse newvars ++ vars) rest res

instance (BaseType :<< t, KappaType :<< t) => TypePrim t (Const KappaPrim) where
  typePrim = \case
    Const KConstBool ->
      mono $
        typeCtor BTBool ~>
        (typeDynOf $ typeCtor KTBool #: nil)

    Const KConstDbl ->
      mono $
        typeCtor BTFloat ~>
        (typeDynOf $ typeCtor KTFloat #: nil)

    Const KConstVec ->
      mono $
        typeListOf (typeCtor BTFloat) ~>
        (typeDynOf $ typeVectorOf (typeCtor KTFloat) #: nil)

    Const (KPrim EAdd) ->
      mono $
        (typeDynOf $ typeCtor KTFloat #: nil) ~>
        (typeDynOf $ typeCtor KTFloat #: nil) ~>
        (typeDynOf $ typeCtor KTFloat #: nil)

    Const (KPrim EMul) ->
      mono $
        (typeDynOf $ typeCtor KTFloat #: nil) ~>
        (typeDynOf $ typeCtor KTFloat #: nil) ~>
        (typeDynOf $ typeCtor KTFloat #: nil)

    Const (KPrim ESub) ->
      mono $
        (typeDynOf $ typeCtor KTFloat #: nil) ~>
        (typeDynOf $ typeCtor KTFloat #: nil) ~>
        (typeDynOf $ typeCtor KTFloat #: nil)

    Const (KPrim EDiv) ->
      mono $
        (typeDynOf $ typeCtor KTFloat #: nil) ~>
        (typeDynOf $ typeCtor KTFloat #: nil) ~>
        (typeDynOf $ typeCtor KTFloat #: nil)

    Const (KPrim EMap) ->
      forall EStar $ \a ->
      forall EStar $ \b ->
      mono $
        (typeDynOf (a #: nil) ~> typeDynOf (b #: nil)) ~>
        (typeDynOf $ typeVectorOf a #: nil) ~>
        (typeDynOf $ typeVectorOf b #: nil)

    Const (KPrim EFold) ->
      forall EStar $ \a ->
      forall EStack $ \t ->
      mono $
        (typeDynOf (a #: nil) ~> typeDynOf t ~> typeDynOf t) ~>
        (typeDynOf $ typeVectorOf a #: nil) ~>
        (typeDynOf $ t) ~>
        (typeDynOf $ t)

    Const (KPrim ELoop) ->
      forall EStar  $ \a ->
      forall EStar  $ \b ->
      forall EStack $ \t ->
      mono $
        (typeDynOf (a #: nil) ~> typeDynOf (a #: b #: t)) ~>
        (typeDynOf $ b #: t)

    Const (KPrim EBranch) ->
      forall EStar  $ \a ->
      mono $
        (typeDynOf $ typeCtor KTBool #: nil) ~>
        (typeDynOf $ a #: nil) ~>
        (typeDynOf $ a #: nil) ~>
        (typeDynOf $ a #: nil)

    Const KCons ->
      forall EStar $ \a ->
      forall EStack $ \t ->
      mono $
        (typeDynOf $ a #: nil) ~>
        (typeDynOf $ t) ~>
        (typeDynOf $ a #: t)

    Const KFirst ->
      forall EStar $ \a ->
      forall EStack $ \t ->
      mono $
        (typeDynOf $ a #: t) ~>
        (typeDynOf $ a #: nil)

    Const KRest ->
      forall EStar $ \a ->
      forall EStack $ \t ->
      mono $
        (typeDynOf $ a #: t) ~>
        (typeDynOf $ t)

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
  | EFold
  | EMap
  | ELoop
  | EBranch
  deriving (Show, Eq, Ord)

data EExpr
  = EReturn [EValue]
  | ELet [EVar] EPrim [EAbs] [EValue] EExpr
  deriving (Show)

data EAbs = EAbs [EVar] EExpr
  deriving (Show)

data EValue
  = ERef EVar
  | EUnit
  | EBool Bool
  | ELit Double
  | EVec [Double]
  deriving (Show)

fresh :: (Member KappaEffect sig, Carrier sig m) => m EVar
fresh = do
  x <- gets freshVar
  modify (\st -> let EVar n = freshVar st in st { freshVar = EVar (succ n) })
  return x

ekappa :: (Member KappaEffect sig, Carrier sig m) => Int -> ([EVar] -> m a) -> m a
ekappa arity body = do
  modify $ \st -> st
    { focused   = id
    , unfocused = focused st : unfocused st
    }
  vars <- replicateM arity fresh
  -- traceState $ "EKAPPA"
  body vars

eapply :: (Member KappaEffect sig, Carrier sig m) => EPrim -> Int -> [EAbs] -> [EValue] -> m [EValue]
eapply p coarity fs xs = do
  vars <- replicateM coarity fresh
  let entry = ELet vars p fs xs
  modify $ \st -> st { focused = focused st . entry }
  -- traceState $ "EAPPLY " ++ show p ++ " " ++ show xs ++ " " ++ show fs
  pure (map ERef vars)

eunkappa :: (Member RuntimeErrorEffect sig, Member KappaEffect sig, Carrier sig m) => m (EExpr -> EExpr)
eunkappa = do
  expr <- gets focused
  rest <- gets unfocused
  case rest of
    [] -> evalError "eunkappa: can't pop stack anymore"
    (c : cs) -> modify $ \st -> st { focused = c, unfocused = cs }
  pure expr

toEExpr :: (Member RuntimeErrorEffect sig, Member KappaEffect sig, Carrier sig m) => [EValue] -> m EExpr
toEExpr values = do
  expr <- gets focused
  pure $ expr (EReturn values)

----------------------------------------------------------------------

ppEVar :: EVar -> Doc ann
ppEVar (EVar n) = "@" <> pretty n

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
  ELet refs prim fs args rest -> vsep $
    [ "LET" <+> ppTuple (map ppEVar refs) <+> ":=" <+> ppEPrim prim <+> ppTuple (map ppEValue args) ] ++
    map (\fun -> indent 2 $ "WITH" <+> ppEAbs fun) fs ++
    [ ppEExpr rest ]
  EReturn vals ->
    "RET" <+> ppTuple (map ppEValue vals)

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
      , indent 4 (ppEExpr (e (EReturn [])))
      , "----------------------------------------------------------------------"
      ]
