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

module Prim.Base
  ( BaseValue(..)
  , mkVDbl
  , mkVText
  , mkVPair
  , mkVUnit
  , projBase
  , BasePrim(..)
  , partialEff
  ) where

import Control.Effect.Carrier

import Data.Functor.Const
import Data.Functor.Foldable (Fix (..), unfix)
import Data.Sum
import Data.Text (Text)
import qualified Data.Text as T
import Data.Text.Prettyprint.Doc as PP

import Expr
import Pretty
import Types
import Eval
import Utils

data BasePrim
  = Add
  | If
  | ReadDouble
  | ShowDouble
  | Delay
  | ListNil
  | ListCons
  | MkPair
  | MkDouble Double
  | MkText Text
  | MkUnit

data BaseValue e
  = VDbl Double
  | VText Text
  | VPair e e
  | VList [e]
  | VUnit

mkVDbl :: (BaseValue :< v) => Double -> Value v
mkVDbl x = Fix . inject $ VDbl x

mkVText :: (BaseValue :< v) => Text -> Value v
mkVText x = Fix . inject $ VText x

mkVPair :: (BaseValue :< v) => Value v -> Value v -> Value v
mkVPair a b = Fix . inject $ VPair a b

mkVList :: (BaseValue :< v) => [Value v] -> Value v
mkVList xs = Fix . inject $ VList xs

mkVUnit :: (BaseValue :< v) => Value v
mkVUnit = Fix . inject $ VUnit

projBase :: (BaseValue :< v) => Value v -> Maybe (BaseValue (Value v))
projBase = project @BaseValue . unfix

instance Pretty1 BaseValue where
  liftPretty pp = \case
    VDbl x    -> pretty x
    VText x   -> pretty (show x)
    VPair a b -> parens (pp a <+> "**" <+> pp b)
    VList xs  -> list (map pp xs)
    VUnit     -> "Unit"

instance PrettyPrim (Const BasePrim) where
  prettyPrim = \case
    Const Add          -> "Add"
    Const If           -> "If"
    Const ReadDouble   -> "ReadNum"
    Const ShowDouble   -> "ShowNum"
    Const Delay        -> "Delay"
    Const ListNil      -> "Nil"
    Const ListCons     -> "Cons"
    Const MkPair       -> "Pair"
    Const (MkDouble n) -> pretty n
    Const (MkText s)   -> pretty (show s)
    Const MkUnit       -> "Unit"

instance ( Member RuntimeErrorEffect sig
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

      Const ShowDouble ->
        pure $ mkVLam @m $ \x ->
          case projBase x of
            Just (VDbl x') -> pure $ mkVText (T.pack (show x'))
            _ -> evalError "ShowDouble: not a double"

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

      Const ListNil ->
        pure $ mkVList []

      Const ListCons ->
        pure $ mkVLam @m $ \x ->
        pure $ mkVLam @m $ \xs ->
          case projBase xs of
            Just (VList xs') -> pure $ mkVList (x : xs')
            _ -> evalError "Wrong arguments"


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
        case projLambda l of
          Just f -> f mkVUnit
          Nothing -> evalError "Cannot force a non-lambda"

partialEff :: Label
partialEff = Label (T.pack "partial")

instance TypePrim (Const BasePrim) where
  typePrim = \case
    Const Add ->
      mono $
        Fix (T TDouble) ~> Fix (T TDouble) ~> Fix (T TDouble)
    Const ReadDouble ->
      mono $
        Fix (T TText) ~> Fix (T TDouble)
    Const ShowDouble ->
      mono $
        Fix (T TDouble) ~> Fix (T TText)
    Const If ->
      forall Star $ \a ->
      mono $
        Fix (T TDouble) ~> (Fix (T TUnit) ~> a) ~> (Fix (T TUnit) ~> a) ~> a
    Const Delay ->
      forall Star $ \a ->
      mono $
        (Fix (T TUnit) ~> a) ~> (Fix (T TUnit) ~> a)
    Const ListNil ->
      forall Star $ \a ->
      mono $ typeListOf a
    Const ListCons ->
      forall Star $ \a ->
      mono $
        a ~> typeListOf a ~> typeListOf a
    Const MkPair ->
      forall Star $ \a ->
      forall Star $ \b ->
      mono $ a ~> b ~> ((Fix (TCtor "Pair") @: a) @: b)
    Const (MkDouble _) ->
      mono $ Fix $ T $ TDouble
    Const (MkText _) ->
      mono $ Fix $ T $ TText
    Const MkUnit ->
      mono $ Fix $ T $ TUnit
