{-# LANGUAGE DeriveFoldable       #-}
{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DeriveTraversable    #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE UndecidableInstances #-}

module Types
  ( Kind(..)
  , TVar(..)
  , MetaVar(..)
  , Type
  , TypeF(..)
  , Label(..)
  , getRowTail
  , TypePrim(..)
  , TyScheme
  , toType
  , forall
  , mono
  , (~>)
  , (@:)
  , (#:)
  , typeCtor
  , typeListOf
  , typeTupleOf
  , typeVectorOf
  , typeExprOf
  , kindsOfTypes
  ) where

import Control.Monad
import Data.Functor.Classes
import Data.Functor.Classes.Generic
import Data.Functor.Foldable (Fix(..), cata)
import Data.Sum
import Data.Void
import Data.String
import Data.Text (Text)

import GHC.Generics

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

type CtorName = Text

type Type = Fix TypeF
data TypeF e
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
  | TCtor CtorName

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
  | TEArrow e e            -- ESTACK -> ESTAR -> STAR

  deriving (Show, Eq, Ord, Functor, Foldable, Traversable, Generic1)

instance Eq1 TypeF where
  liftEq = liftEqDefault

instance Ord1 TypeF where
  liftCompare = liftCompareDefault

instance Show1 TypeF where
  liftShowsPrec = liftShowsPrecDefault

getRowTail :: Type -> Maybe TVar
getRowTail =
  cata $ \case
    TRowExtend _ _ _ x -> x
    TRef v -> Just v
    other -> msum other

----------------------------------------------------------------------
-- Prims typing algebra

data TyScheme = TyScheme
  { tsForall :: [TVar]
  , tsBody   :: Type
  } deriving (Show, Eq, Ord)

toType :: TyScheme -> Type
toType (TyScheme vars body) =
  foldr (\x rest -> Fix $ TForall x rest) body vars

class TypePrim (p :: * -> *) where
  typePrim :: p Void -> TyScheme

instance (Apply TypePrim ps) => TypePrim (Sum ps) where
  typePrim = apply @TypePrim typePrim

----------------------------------------------------------------------
-- Types DSL

forall :: Kind -> (Type -> TyScheme) -> TyScheme
forall k f =
  let TyScheme bs ty = f (Fix (TRef tv))
      n = case bs of
            [] -> 0
            (TVar m _ : _) -> m + 1
      tv = TVar n k
  in  TyScheme (tv : bs) ty

mono :: Type -> TyScheme
mono ty = TyScheme [] ty

infixr 3 ~>

(~>) :: Type -> Type -> Type
a ~> b = Fix (TArrow a b)

(#:) :: Type -> Type -> Type
(#:) a b = Fix (TSCons a b)
infixr 5 #:

(@:) :: Type -> Type -> Type
(@:) f a = Fix (TApp f a)
infixl 7 @:

typeCtor :: Text -> Type
typeCtor = Fix . TCtor

typeVectorOf :: Type -> Type
typeVectorOf a = (Fix (TCtor "EVec") @: a)

typeTupleOf :: Type -> Type
typeTupleOf a = Fix (TCtor "ETuple") @: a

typeListOf :: Type -> Type
typeListOf a = (Fix (TCtor "List") @: a)

typeExprOf :: Type -> Type
typeExprOf r = Fix (TEArrow (Fix TSNil) r)

kindsOfTypes :: [(CtorName, Kind)]
kindsOfTypes =
  [ "Float"   %:: Star
  , "Bool"    %:: Star
  , "Unit"    %:: Star
  , "Text"    %:: Star
  , "List"    %:: Star `Arr` Star
  , "EVec"    %:: EStar `Arr` EStar
  , "ETuple"  %:: EStack `Arr` EStar
  , "EFloat"  %:: EStar
  ]
  where
    (%::) = (,)
    infix 1 %::
