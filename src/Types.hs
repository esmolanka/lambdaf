{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE DeriveFoldable         #-}
{-# LANGUAGE DeriveFunctor          #-}
{-# LANGUAGE DeriveGeneric          #-}
{-# LANGUAGE DeriveTraversable      #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}

module Types
  ( Kind(..)
  , TVar(..)
  , MetaVar(..)
  , Type
  , TypeF(..)
  , Label(..)
  , getRowTail
  , TypePrim(..)
  , KindOfCtor(..)
  , TypeConstructor
  , TyScheme
  , toType
  , forall
  , mono
  , (~>)
  , (@:)
  , (#:)
  , nil
  , typeCtor
  ) where

import Control.Monad
import Data.Functor.Classes
import Data.Functor.Classes.Generic
import Data.Functor.Foldable (Fix(..), cata)
import Data.String
import Data.Sum
import Data.Text (Text)
import Data.Void
import GHC.Generics

import Utils

newtype Label = Label Text
    deriving (Show, Eq, Ord)

instance IsString Label where
  fromString = Label . fromString

data Kind
  = Arr Kind Kind
  | Star
  | Row
  | Presence
  | EStar
  | EStack
  deriving (Show, Eq, Ord)

data TVar = TVar
  { tvName :: Int
  , tvKind :: Kind
  } deriving (Show, Eq, Ord)

data MetaVar = MetaVar
  { etvName :: Int
  , etvKind :: Kind
  } deriving (Show, Eq, Ord)

type Type p = Fix (TypeF p)
data TypeF (p :: [*]) e
  ----------------------------------------------------------------------
  -- Base language
  = TRef    TVar           -- κ
  | TMeta   MetaVar        -- κ
  | TApp    e e
  | TArrow  e e            -- STAR -> ROW -> STAR -> STAR
  | TForall TVar e         -- κ
  | TExists TVar e         -- κ

  | TUnit
  | TVoid

  ----------------------------------------------------------------------
  -- User-defined types
  | TCtor (Sum' p)

  ----------------------------------------------------------------------
  -- Row typed records and variants
  | TRecord  e             -- ROW -> STAR
  | TVariant e             -- ROW -> STAR

  | TPresent               -- PRESENCE
  | TAbsent                -- PRESENCE

  | TRowEmpty              -- ROW
  | TRowExtend Label e e e -- PRESENCE -> STAR -> ROW -> ROW

  ----------------------------------------------------------------------
  -- Embedded language types
  | TSNil                  -- ESTACK
  | TSCons  e e            -- ESTAR -> ESTACK -> ESTACK

  deriving (Functor, Foldable, Traversable, Generic1)

instance (Apply Eq1 (Map Const t)) => Eq1 (TypeF t) where
  liftEq = liftEqDefault

instance (Apply Eq1 (Map Const t), Apply Ord1 (Map Const t)) => Ord1 (TypeF t) where
  liftCompare = liftCompareDefault

instance (Apply Show1 (Map Const t)) => Show1 (TypeF t) where
  liftShowsPrec = liftShowsPrecDefault

getRowTail :: Type t -> Maybe TVar
getRowTail =
  cata $ \case
    TRowExtend _ _ _ x -> x
    TRef v -> Just v
    other -> msum other

----------------------------------------------------------------------
-- Prims typing algebra

class TypePrim (t :: [*]) (p :: * -> *) where
  typePrim :: p Void -> TyScheme t

instance forall t ps. (Apply (TypePrim t) ps) => TypePrim t (Sum ps) where
  typePrim = apply @(TypePrim t) typePrim

class KindOfCtor (t :: * -> *) where
  kindOfCtor :: t Void -> Kind

instance (Apply KindOfCtor ts) => KindOfCtor (Sum ts) where
  kindOfCtor = apply @KindOfCtor kindOfCtor

type TypeConstructor t =
  ( Apply Eq1        (Map Const t)
  , Apply Show1      (Map Const t)
  , Apply Pretty1    (Map Const t)
  , Apply KindOfCtor (Map Const t)
  )

typeCtor :: (t :<< ts) => t -> Type ts
typeCtor = Fix . TCtor . inject'

----------------------------------------------------------------------
-- Types DSL

data TyScheme t = TyScheme
  { _tsForall :: [TVar]
  , _tsBody   :: Type t
  }

toType :: TyScheme t -> Type t
toType (TyScheme vars body) =
  foldr (\x rest -> Fix $ TForall x rest) body vars

forall :: Kind -> (Type t -> TyScheme t) -> TyScheme t
forall k f =
  let TyScheme bs ty = f (Fix (TRef tv))
      n = case bs of
            [] -> 0
            (TVar m _ : _) -> m + 1
      tv = TVar n k
  in  TyScheme (tv : bs) ty

mono :: Type t -> TyScheme t
mono ty = TyScheme [] ty

infixr 3 ~>

(~>) :: Type t -> Type t -> Type t
a ~> b = Fix (TArrow a b)

(#:) :: Type t -> Type t -> Type t
(#:) a b = Fix (TSCons a b)
infixr 5 #:

nil :: Type t
nil = Fix TSNil

(@:) :: Type t -> Type t -> Type t
(@:) f a = Fix (TApp f a)
infixl 7 @:
