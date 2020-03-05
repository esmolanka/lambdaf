{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MonoLocalBinds             #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}

module Expr
  ( Expr
  , ExprF(..)
  , Value
  , Variable(..)
  , LambdaValue(..)
  , mkVLam
  , projLambda
  ) where

import Data.Functor.Foldable (Fix (..), unfix)
import Data.Sum
import qualified Data.Text as T

import Syntax.Position
import Utils
import Types

newtype Variable = Variable T.Text
  deriving (Eq, Ord, Show)

type Expr (p :: [*]) = Fix (ExprF p)
type Value (l :: [* -> *]) = Fix (Sum l)

data ExprF (p :: [*]) e
  = Ref    Position Variable
  | Lambda Position Variable e
  | App    Position e e
  | Let    Position Variable e e
  | Annot  Position e Type
  | Prim   Position (Sum' p)
    deriving (Functor)

data LambdaValue m e
  = VLam (e -> m e)

mkVLam :: forall m v. (LambdaValue m :< v) => (Value v -> m (Value v)) -> Value v
mkVLam x = Fix . inject $ VLam x

projLambda :: forall m v. (LambdaValue m :< v) => Value v -> Maybe (LambdaValue m (Value v))
projLambda = project @(LambdaValue m) . unfix

instance Pretty1 (LambdaValue m) where
  liftPretty _pp = \case
    VLam _ -> "<Lambda>"
