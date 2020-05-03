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
  , mkVFloat
  , mkVBool
  , mkVText
  , mkVUnit
  , projBase
  , BasePrim(..)
  , partialEff
  , BaseType(..)
  , typeListOf
  ) where

import Control.Effect.Carrier

import Data.Functor.Const
import Data.Functor.Foldable (Fix (..), unfix)
import Data.Sum
import Data.Text (Text)
import qualified Data.Text as T
import Data.Text.Prettyprint.Doc as PP

import Expr
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
  | MkBool Bool
  | MkFloat Double
  | MkText Text
  | MkUnit

data BaseType
  = BTFloat
  | BTBool
  | BTText
  | BTList
    deriving (Eq, Show)

typeListOf :: (BaseType :<< t) => Type t -> Type t
typeListOf a = typeCtor BTList @: a

instance Pretty BaseType where
  pretty = \case
    BTFloat -> "Float"
    BTBool -> "Bool"
    BTText -> "Text"
    BTList -> "List"

instance KindOfCtor (Const BaseType) where
  kindOfCtor = \case
    Const BTFloat -> Star
    Const BTBool -> Star
    Const BTText -> Star
    Const BTList -> Star `Arr` Star

data BaseValue e
  = VFloat Double
  | VBool Bool
  | VText Text
  | VList [e]
  | VUnit

mkVFloat :: (BaseValue :< v) => Double -> Value v
mkVFloat x = Fix . inject $ VFloat x

mkVBool :: (BaseValue :< v) => Bool -> Value v
mkVBool x = Fix . inject $ VBool x

mkVText :: (BaseValue :< v) => Text -> Value v
mkVText x = Fix . inject $ VText x

mkVList :: (BaseValue :< v) => [Value v] -> Value v
mkVList xs = Fix . inject $ VList xs

mkVUnit :: (BaseValue :< v) => Value v
mkVUnit = Fix . inject $ VUnit

projBase :: (BaseValue :< v) => Value v -> Maybe (BaseValue (Value v))
projBase = project @BaseValue . unfix

instance Pretty1 BaseValue where
  liftPretty pp = \case
    VFloat x  -> pretty x
    VBool x   -> pretty x
    VText x   -> pretty (show x)
    VList xs  -> list (map pp xs)
    VUnit     -> "Unit"

instance Pretty BasePrim where
  pretty = \case
    Add         -> "Add"
    If          -> "If"
    ReadDouble  -> "ReadNum"
    ShowDouble  -> "ShowNum"
    Delay       -> "Delay"
    ListNil     -> "Nil"
    ListCons    -> "Cons"
    (MkBool b)  -> pretty b
    (MkFloat n) -> pretty n
    (MkText s)  -> pretty (show s)
    MkUnit      -> "Unit"

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
            Just (VFloat x') ->
              case projBase y of
                Just (VFloat y') -> pure $ mkVFloat (x' + y')
                _ -> evalError "RHS is not a double!"
            _ -> evalError "LHS is not a double!"

      Const ReadDouble ->
        pure $ mkVLam @m $ \x ->
          case projBase x of
            Just (VText x') ->
              case reads (T.unpack x') of
                [(dbl,"")] -> pure $ mkVFloat dbl
                _          -> evalError ("Could not read double: " ++ show x')
            _ -> evalError "ReadDouble: not a string"

      Const ShowDouble ->
        pure $ mkVLam @m $ \x ->
          case projBase x of
            Just (VFloat x') -> pure $ mkVText (T.pack (show x'))
            _ -> evalError "ShowDouble: not a double"

      Const If ->
        pure $ mkVLam @m $ \c ->
        pure $ mkVLam @m $ \t ->
        pure $ mkVLam @m $ \f ->
          case projBase c of
            Just (VFloat c')
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

      Const (MkBool b) ->
        pure $ mkVBool b

      Const (MkFloat n) ->
        pure $ mkVFloat n

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

instance (BaseType :<< t) => TypePrim t (Const BasePrim) where
  typePrim = \case
    Const Add ->
      mono $
        typeCtor BTFloat ~> typeCtor BTFloat ~> typeCtor BTFloat
    Const ReadDouble ->
      mono $
        typeCtor BTText ~> typeCtor BTFloat
    Const ShowDouble ->
      mono $
        typeCtor BTFloat ~> typeCtor BTText
    Const If ->
      forall Star $ \a ->
      mono $
        typeCtor BTFloat ~> (Fix TUnit ~> a) ~> (Fix TUnit ~> a) ~> a
    Const Delay ->
      forall Star $ \a ->
      mono $
        (Fix TUnit ~> a) ~> (Fix TUnit ~> a)
    Const ListNil ->
      forall Star $ \a ->
      mono $ typeListOf a
    Const ListCons ->
      forall Star $ \a ->
      mono $
        a ~> typeListOf a ~> typeListOf a
    Const (MkBool _) ->
      mono $ typeCtor BTBool
    Const (MkFloat _) ->
      mono $ typeCtor BTFloat
    Const (MkText _) ->
      mono $ typeCtor BTText
    Const MkUnit ->
      mono $ Fix TUnit
