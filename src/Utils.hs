{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE UndecidableInstances       #-}

module Utils
  ( module Utils
  , Const(..)
  , Pretty(..)
  ) where

import Data.Functor.Const
import Data.Sum
import Data.Text.Prettyprint.Doc as PP
import Data.Void
import Data.Kind

type family Map (f :: * -> * -> *) (xs :: [*]) where
  Map f '[]       = '[]
  Map f (x ': xs) = f x ': Map f xs

type Sum' es = Sum (Map Const es) Void

inject' :: (Const e :< r) => e -> Sum r v
inject' = inject . Const

type (:<<) l ls = (Const l :< Map Const ls)

class Pretty1 (f :: * -> *) where
  liftPretty :: (a -> Doc ann) -> f a -> Doc ann

instance (Apply Pretty1 ps) => Pretty1 (Sum ps) where
  liftPretty f = apply @Pretty1 (liftPretty f)

instance Pretty a => Pretty1 (Const a) where
  liftPretty _ (Const a) = pretty a

type Apply' (c :: (* -> *) -> Constraint) (t :: [*]) = c (Sum (Map Const t))
