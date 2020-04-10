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

mkVVariant :: (VariantValue :< v) => Label -> Value v -> Value v
mkVVariant lbl = Fix . inject . VVariant lbl

instance Pretty1 VariantValue where
  liftPretty pp = \case
    VVariant lbl p ->
      ppLabel lbl <> parens (pp p)

instance PrettyPrim (Const VariantPrim) where
  prettyPrim = \case
    Const (VariantInject lbl)  -> "VariantInject" <> angles (ppLabel lbl)
    Const (VariantDecomp lbl)  -> "VariantDecomp" <> angles (ppLabel lbl)
    Const VariantAbsurd        -> "VariantAbsurd"

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

instance TypePrim (Const VariantPrim) where
  typePrim = \case
    Const (VariantInject label) ->
      forall Star $ \a ->
      forall Row  $ \r ->
      mono $
        a ~> Fix (TVariant (Fix (TRowExtend label (Fix TPresent) a r)))

    -- VariantDecomp<lbl> : (a -> b) -> (<r> -> b) -> <lbl? : a | r> -> b
    Const (VariantDecomp label) ->
      forall Star $ \a ->
      forall Star $ \b ->
      forall Presence $ \p ->
      forall Row  $ \r ->
      mono $
        (a ~> b) ~>
        (Fix (TVariant r) ~> b) ~>
        (Fix $ TVariant $ Fix $ TRowExtend label p a r) ~> b

    Const VariantAbsurd ->
      forall Star $ \a ->
      mono $
        Fix (TVariant (Fix TRowEmpty)) ~> a
