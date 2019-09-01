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

module Prim.Base where

import Control.Effect.Carrier
import Control.Effect.Error

import Data.Functor.Classes
import Data.Functor.Const
import Data.Functor.Foldable (Fix (..), unfix)
import Data.Sum
import Data.Text (Text)
import qualified Data.Text as T
import Data.Text.Prettyprint.Doc as PP

import Expr
import Pretty
import Syntax.Position
import Types
import Utils

data BasePrim
  = Add
  | If
  | ReadDouble
  | Delay
  | MkPair
  | MkDouble Double
  | MkText Text
  | MkUnit

data BaseValue e
  = VDbl Double
  | VText Text
  | VPair e e
  | VUnit

mkVDbl :: (BaseValue :< v) => Double -> Value v
mkVDbl x = Fix . inject $ VDbl x

mkVText :: (BaseValue :< v) => Text -> Value v
mkVText x = Fix . inject $ VText x

mkVPair :: (BaseValue :< v) => Value v -> Value v -> Value v
mkVPair a b = Fix . inject $ VPair a b

mkVUnit :: (BaseValue :< v) => Value v
mkVUnit = Fix . inject $ VUnit

instance Show1 BaseValue where
  liftShowsPrec sp _sl _n = \case
    VDbl x    -> showString "#" . shows x
    VText x   -> shows x
    VPair a b -> showString "(" . sp 0 a . showString " ** " . sp 0 b . showString ")"
    VUnit     -> showString "Unit"

instance Pretty1 BaseValue where
  liftPretty pp = \case
    VDbl x    -> pretty x
    VText x   -> pretty (show x)
    VPair a b -> parens (pp a <+> "**" <+> pp b)
    VUnit     -> "Unit"

instance PrettyPrim (Const BasePrim) where
  prettyPrim = \case
    Const Add          -> "Add"
    Const If           -> "If"
    Const ReadDouble   -> "ReadNum"
    Const Delay        -> "Delay"
    Const MkPair       -> "Pair"
    Const (MkDouble n) -> pretty n
    Const (MkText s)   -> pretty (show s)
    Const MkUnit       -> "Unit"

instance ( Member (Error String) sig
         , Carrier sig m
         , LambdaValue m :< v
         , BaseValue :< v
         ) => EvalPrim m v (Const BasePrim) where
  evalPrim = \case
      Const Add ->
        pure $ mkVLam @m $ \x ->
        pure $ mkVLam @m $ \y ->
          case projBase x of
            Just (VDbl x') ->
              case projBase y of
                Just (VDbl y') -> pure $ mkVDbl (x' + y')
                _ -> evalError "RHS is not a double!"
            _ -> evalError "LHS is not a double!"

      Const ReadDouble ->
        pure $ mkVLam @m $ \x ->
          case projBase x of
            Just (VText x') ->
              case reads (T.unpack x') of
                [(dbl,"")] -> pure $ mkVDbl dbl
                _          -> evalError ("Could not read double: " ++ show x')
            _ -> evalError "ReadDouble: not a string"

      Const If ->
        pure $ mkVLam @m $ \c ->
        pure $ mkVLam @m $ \t ->
        pure $ mkVLam @m $ \f ->
          case projBase c of
            Just (VDbl c')
              | c' > 0    -> forceDelayed t
              | otherwise -> forceDelayed f
            _ -> evalError "Condition is not a double!"

      Const Delay ->
        pure $ mkVLam @m $ \f ->
        pure $ mkVLam @m $ \u ->
          case projBase u of
            Just VUnit -> forceDelayed f
            _ -> evalError "Delay expects a unit"

      Const MkPair ->
        pure $ mkVLam @m $ \a ->
        pure $ mkVLam @m $ \b ->
          pure (mkVPair a b)

      Const (MkDouble n) ->
        pure $ mkVDbl n

      Const (MkText t) ->
        pure $ mkVText t

      Const MkUnit ->
        pure $ mkVUnit
    where
      forceDelayed l =
        case projLam l of
          Just (VLam f) -> f mkVUnit
          Nothing -> evalError "Cannot force a non-lambda"

      projLam :: (LambdaValue m :< v) => Value v -> Maybe (LambdaValue m (Value v))
      projLam = project @(LambdaValue m) . unfix

      projBase :: (BaseValue :< v) => Value v -> Maybe (BaseValue (Value v))
      projBase = project @BaseValue . unfix

partialEff :: Label
partialEff = Label (T.pack "partial")

instance TypePrim (Const BasePrim) where
  typePrim = \case
    Const Add ->
      effect $ \e1 ->
      effect $ \e2 ->
      mono $
        (Fix (T TDouble), e1) ~>
        (Fix (T TDouble), e2) ~> Fix (T TDouble)
    Const ReadDouble ->
      effect $ \e1 ->
      mono $
        (Fix (T TText), Fix (TRowExtend partialEff (Fix TPresent) (Fix (T TUnit)) e1)) ~>
        (Fix (T TDouble))
    Const If ->
      forall Star $ \a ->
      effect $ \e1 ->
      effect $ \e2 ->
      effect $ \e3 ->
      mono $
        (Fix (T TDouble), e1) ~>
        ((Fix (T TUnit), e3) ~> a, e2) ~>
        ((Fix (T TUnit), e3) ~> a, e3) ~> a
    Const Delay ->
      forall Star $ \a ->
      effect $ \e1 ->
      effect $ \e2 ->
      mono $
        ((Fix (T TUnit), e1) ~> a, e2) ~>
        ((Fix (T TUnit), e1) ~> a)
    Const MkPair ->
      forall Star $ \a ->
      forall Star $ \b ->
      effect $ \e1 ->
      effect $ \e2 ->
      mono $ (a, e1) ~> (b, e2) ~> Fix (TPair a b)
    Const (MkDouble _) ->
      mono $ Fix $ T $ TDouble
    Const (MkText _) ->
      mono $ Fix $ T $ TText
    Const MkUnit ->
      mono $ Fix $ T $ TUnit

----------------------------------------------------------------------

prim :: (BasePrim :<< p) => BasePrim -> Expr p
prim p = Fix (Prim dummyPos (inject' p))

if_ :: (BasePrim :<< p) => Expr p -> Expr p -> Expr p -> Expr p
if_ c t f = prim If ! c ! t ! f

lit :: (BasePrim :<< p) => Double -> Expr p
lit n = prim (MkDouble n)

txt :: (BasePrim :<< p) => String -> Expr p
txt t = prim (MkText (T.pack t))

(**) :: (BasePrim :<< p) => Expr p -> Expr p -> Expr p
(**) a b = prim MkPair ! a ! b

infixr 3 **