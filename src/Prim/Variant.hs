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

module Prim.Variant where

import Control.Effect.Carrier

import Data.Functor.Const
import Data.Functor.Foldable (Fix (..), unfix)
import Data.Sum
import Data.Text.Prettyprint.Doc as PP

import Expr
import Eval
import Pretty
import Types
import Utils

data VariantPrim
  = VariantInject Label
  | VariantDecomp Label
  | VariantAbsurd

data VariantValue e
  = VVariant Label e

data VariantType
  = TVariant
    deriving (Eq, Show)

mkVVariant :: (VariantValue :< v) => Label -> Value v -> Value v
mkVVariant lbl = Fix . inject . VVariant lbl

instance Pretty1 VariantValue where
  liftPretty pp = \case
    VVariant lbl p ->
      ppLabel lbl <> parens (pp p)

instance Pretty VariantPrim where
  pretty = \case
    VariantInject lbl -> "VariantInject" <> angles (ppLabel lbl)
    VariantDecomp lbl -> "VariantDecomp" <> angles (ppLabel lbl)
    VariantAbsurd     -> "VariantAbsurd"

instance PrettyType (Const VariantType) where
  prettySpine _lvl = \case
    (Const TVariant, [a]) -> Just $ angles (align $ a 0)
    _ -> Nothing
  prettyCtor = \case
    Const TVariant -> "Variant"

instance KindOfCtor (Const VariantType) where
  kindOfCtor = \case
    Const TVariant   -> Row `Arr` Star

typeVariantOf :: (VariantType :<< t) => Type t -> Type t
typeVariantOf r = typeCtor TVariant @: r

instance ( Member RuntimeErrorEffect sig
         , Carrier sig m
         , LambdaValue m :< v
         , VariantValue :< v
         ) => EvalPrim m v (Const VariantPrim) where
  evalPrim = \case
    Const (VariantInject lbl) ->
      pure $ mkVLam @m $ \a ->
        pure $ mkVVariant lbl a

    Const (VariantDecomp lbl) ->
      pure $ mkVLam @m $ \g ->
      pure $ mkVLam @m $ \f ->
      pure $ mkVLam @m $ \v ->
        case projLambda g of
          Just g' ->
            case projLambda f of
              Just f' ->
                case projVariant v of
                  Just (VVariant lbl' p) | lbl == lbl' -> g' p
                                         | otherwise   -> f' v
                  _ -> evalError "VariantDecomp: not a variant"
              _ -> evalError "VariantDecomp: not a function"
          _ -> evalError "VariantDecomp: not a function"

    Const VariantAbsurd ->
      pure $ mkVLam @m $ \_ ->
        evalError "VariantAbsurd: constructed absurd"

    where
      projVariant = project @VariantValue . unfix

instance (VariantType :<< t) => TypePrim t (Const VariantPrim) where
  typePrim = \case
    Const (VariantInject label) ->
      forall Star $ \a ->
      forall Row  $ \r ->
      mono $
        a ~> typeVariantOf (Fix (TRowExtend label (Fix TPresent) a r))

    -- VariantDecomp<lbl> : (a -> b) -> (<r> -> b) -> <lbl? : a | r> -> b
    Const (VariantDecomp label) ->
      forall Star $ \a ->
      forall Star $ \b ->
      forall Presence $ \p ->
      forall Row  $ \r ->
      mono $
        (a ~> b) ~>
        (typeVariantOf r ~> b) ~>
        (typeVariantOf $ Fix $ TRowExtend label p a r) ~> b

    Const VariantAbsurd ->
      forall Star $ \a ->
      mono $
        typeVariantOf (Fix TRowEmpty) ~> a
