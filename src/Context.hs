{-# LANGUAGE DeriveFoldable      #-}
{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE DeriveTraversable   #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module Context
  ( Context (..)
  , empty
  , lookup
  , extend
  , with
  , withSubst
  ) where

import Prelude hiding (lookup)

import Control.Effect.Reader
import Data.Map (Map)
import qualified Data.Map as M

import Expr (Variable)
import Types

newtype Context = Context (Map Variable [TyScheme])

instance Types Context where
  applySubst subst (Context m) =
    Context $ M.map (map (applySubst subst)) m

  freeTyVars (Context c) =
    foldMap (foldMap freeTyVars) c

empty :: Context
empty = Context M.empty

lookup :: Variable -> Int -> Context -> Maybe TyScheme
lookup v n (Context c) =
  case snd . splitAt n . M.findWithDefault [] v $ c of
    [] -> Nothing
    (x : _) -> Just x

extend :: Variable -> TyScheme -> Context -> Context
extend x e (Context c) =
  Context $ M.alter (addEntry e) x $ c
  where
    addEntry :: TyScheme -> Maybe [TyScheme] -> Maybe [TyScheme]
    addEntry a Nothing = Just [a]
    addEntry a (Just as) = Just (a : as)

with :: (Member (Reader Context) sig, Carrier sig m) => Variable -> TyScheme -> m a -> m a
with x t = local (extend x t)

withSubst :: (Member (Reader Context) sig, Carrier sig m) => TySubst -> m a -> m a
withSubst subst =
  local @Context (applySubst subst)
