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
  , exprPosition
  , Value
  , Variable(..)
  , LambdaValue(..)
  , mkVLam
  , projLambda
  ) where

import Data.Fix (Fix (..))
import Data.Sum
import qualified Data.Text as T

import Syntax.Position
import Utils
import Types

newtype Variable = Variable T.Text
  deriving (Eq, Ord, Show)

type Expr (t :: [*]) (p :: [*]) = Fix (ExprF t p)
type Value (l :: [* -> *]) = Fix (Sum l)

data ExprF (t :: [*]) (p :: [*]) e
  = Ref    Position Variable
  | Lambda Position Variable e
  | App    Position e e
  | Let    Position Variable e e
  | Annot  Position e (Type t)
  | Prim   Position (Sum' p)
    deriving (Functor)

exprPosition :: Expr t p -> Position
exprPosition (Fix e) = case e of
  Ref pos _  -> pos
  Lambda pos _ _ -> pos
  App pos _ _ -> pos
  Let pos _ _ _ -> pos
  Annot pos _ _ -> pos
  Prim pos _ -> pos

newtype LambdaValue m e
  = VLam (e -> m e)

mkVLam :: forall m v. (LambdaValue m :< v) => (Value v -> m (Value v)) -> Value v
mkVLam x = Fix . inject $ VLam x

projLambda :: forall m v. (LambdaValue m :< v) => Value v -> Maybe (Value v -> m (Value v))
projLambda = fmap (\(VLam f) -> f) . project @(LambdaValue m) . unFix

instance Pretty1 (LambdaValue m) where
  liftPretty _pp = \case
    VLam _ -> "<Lambda>"
