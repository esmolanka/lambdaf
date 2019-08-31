{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE TypeFamilies               #-}

module Utils where

import Data.Functor.Const
import Data.Sum
import Data.Void

type family Map (f :: * -> * -> *) (xs :: [*]) where
  Map f '[]       = '[]
  Map f (x ': xs) = f x ': Map f xs

type Sum' es = Sum (Map Const es) Void

inject' :: (Const e :< r) => e -> Sum r v
inject' = inject . Const

type (:<<) l ls = (Const l :< Map Const ls)
