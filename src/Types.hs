{-# LANGUAGE DeriveFoldable       #-}
{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DeriveTraversable    #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE UndecidableInstances #-}

module Types where

import Data.Foldable
import Data.Functor.Classes
import Data.Functor.Classes.Generic
import Data.Functor.Foldable (Fix(..), cata)
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Sum
import Data.Void
import Data.String
import Data.Text (Text)

import GHC.Generics

newtype Label = Label Text
    deriving (Show, Eq, Ord)

instance IsString Label where
  fromString = Label . fromString

class Types a where
  freeTyVars :: a -> S.Set TyVar
  applySubst :: TySubst -> a -> a

data Kind
  = Star
  | Row
  | Presence
  | EStar
  deriving (Show, Eq, Ord)

data TyVar = TyVar
  { tvName :: Int
  , tvKind :: Kind
  } deriving (Show, Eq, Ord)

data BaseType
  = TUnit
  | TDouble
  | TText
  deriving (Show, Eq, Ord)

data EType
  = TEDouble
  deriving (Show, Eq, Ord)

type Type = Fix TypeF
data TypeF e
  = TVar TyVar             -- κ
  | T BaseType             -- STAR
  | TArrow e e e           -- STAR -> ROW -> STAR -> STAR
  | TPair e e              -- STAR -> STAR

  | TRecord e              -- ROW -> STAR
  | TVariant e             -- ROW -> STAR

  | TPresent               -- PRESENCE
  | TAbsent                -- PRESENCE

  | TRowEmpty              -- ROW
  | TRowExtend Label e e e -- PRESENCE -> STAR -> ROW -> ROW

  | TE EType               -- ANF
  | TExpr e                -- ANF -> STAR
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable, Generic1)

instance Eq1 TypeF where
  liftEq = liftEqDefault

instance Ord1 TypeF where
  liftCompare = liftCompareDefault

instance Show1 TypeF where
  liftShowsPrec = liftShowsPrecDefault

instance Types Type where
  freeTyVars =
    cata $ \case
      TVar var -> S.singleton var
      other -> fold other

  applySubst (TySubst s) = cata alg
    where
      alg :: TypeF Type -> Type
      alg = \case
        TVar var ->
          case M.lookup var s of
            Just ty -> ty
            Nothing -> Fix (TVar var)
        other -> Fix other

getRowTail :: Type -> Maybe TyVar
getRowTail =
  cata $ \case
    TRowExtend _ _ _ x -> x
    TVar v -> Just v
    other -> msum other


data TyScheme = TyScheme
  { tsForall :: [TyVar]
  , tsBody   :: Type
  } deriving (Show, Eq, Ord)

instance Types TyScheme where
  freeTyVars ts =
    freeTyVars (tsBody ts) `S.difference` S.fromList (tsForall ts)

  applySubst (TySubst s) (TyScheme binders body) =
    let dummy = M.fromList $ map (\tv -> (tv, ())) binders
        subst = TySubst (s `M.difference` dummy)
    in TyScheme binders (applySubst subst body)


data TySubst = TySubst (M.Map TyVar Type)
  deriving (Show, Eq, Ord)

emptySubst :: TySubst
emptySubst = TySubst M.empty

singletonSubst :: TyVar -> Type -> TySubst
singletonSubst tv typ = TySubst (M.singleton tv typ)

simultaneousSubst :: [(TyVar, Type)] -> TySubst
simultaneousSubst subs = TySubst (M.fromList subs)

composeSubst :: TySubst -> TySubst -> TySubst
composeSubst (TySubst a) (TySubst b) =
  TySubst $ M.union
    (M.map (applySubst (TySubst a)) b) a

foldSubsts :: [TySubst] -> TySubst
foldSubsts = foldr composeSubst emptySubst

domSubst :: TyVar -> TySubst -> Bool
domSubst tv (TySubst m) = M.member tv m


----------------------------------------------------------------------
-- Prims typing algebra

class TypePrim (p :: * -> *) where
  typePrim :: p Void -> TyScheme

instance (Apply TypePrim ps) => TypePrim (Sum ps) where
  typePrim = apply @TypePrim typePrim

----------------------------------------------------------------------
-- Types DSL

forall :: Kind -> (Type -> TyScheme) -> TyScheme
forall k f =
  let TyScheme bs ty = f (Fix (TVar tv))
      n = case bs of
            [] -> 0
            (TyVar m _ : _) -> m + 1
      tv = TyVar n k
  in  TyScheme (tv : bs) ty

effect :: (Type -> TyScheme) -> TyScheme
effect f = forall Row f

mono :: Type -> TyScheme
mono ty = TyScheme [] ty

infixr 3 ~>

(~>) :: (Type, Type) -> Type -> Type
(a, e) ~> b = Fix (TArrow a e b)
