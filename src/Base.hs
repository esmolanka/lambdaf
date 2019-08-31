{-# LANGUAGE DataKinds                  #-}
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

module Base where

import Control.Effect.Carrier
import Control.Effect.Error

import qualified Data.Text as T
import Data.Text (Text)
import Data.Functor.Classes
import Data.Functor.Const
import Data.Functor.Foldable (Fix (..), unfix)
import Data.Sum

import Expr
import Utils
import Position

import Types

data BasePrim
  = Add
  | If
  | ReadDouble
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
                _ -> throwError "RHS is not a double!"
            _ -> throwError "LHS is not a double!"

      Const ReadDouble ->
        pure $ mkVLam @m $ \x ->
          case projBase x of
            Just (VText x') ->
              case reads (T.unpack x') of
                [(dbl,"")] -> pure $ mkVDbl dbl
                _          -> throwError ("Could not read double: " ++ show x')
            _ -> throwError "ReadDouble: not a string"

      Const If ->
        pure $ mkVLam @m $ \c ->
        pure $ mkVLam @m $ \t ->
        pure $ mkVLam @m $ \f ->
          case projBase c of
            Just (VDbl c')
              | c' > 0    -> forceDelayed t
              | otherwise -> forceDelayed f
            _ -> throwError "Condition is not a double!"

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
          Nothing -> throwError "Cannot force a non-lambda"

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
    Const MkPair ->
      forall Star $ \a ->
      forall Star $ \b ->
      effect $ \e1 ->
      effect $ \e2 ->
      mono $
        (a, e1) ~>
        (b, e2) ~> Fix (TPair a b)
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
