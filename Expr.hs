{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MonoLocalBinds             #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeOperators              #-}
-- :-/
{-# LANGUAGE UndecidableInstances       #-}

module Expr where

import Control.Effect.Error
import Control.Effect.Reader

import Data.Functor.Classes
import Data.Functor.Const
import Data.Functor.Foldable (Fix (..), unfix, cata)
import qualified Data.Map as M
import Data.Sum
import Data.Void

import Utils
import Position

type Variable = Int

type Expr (p :: [*]) = Fix (ExprF p)
type Value (l :: [* -> *]) = Fix (Sum l)

data ExprF (p :: [*]) e
  = Ref    Position Variable
  | Lambda Position Variable e
  | App    Position e e
  | Prim   Position (Sum' p)
    deriving (Functor)

data LambdaValue m e
  = VLam (e -> m e)

mkVLam :: forall m v. (LambdaValue m :< v) => (Value v -> m (Value v)) -> Value v
mkVLam x = Fix . inject $ VLam x

instance Show1 (LambdaValue m) where
  liftShowsPrec _sp _sl _n = \case
    VLam _    -> showString "<Lambda>"

class EvalPrim m v (p :: * -> *) where
  evalPrim :: p Void -> m (Value v)

instance (Apply (EvalPrim m v) ps) => EvalPrim m v (Sum ps) where
  evalPrim = apply @(EvalPrim m v) evalPrim

eval :: forall m sig (p :: [*]) (v :: [* -> *]).
  ( Member (Error String) sig -- MonadError String m
  , Member (Reader (M.Map Variable (Value v))) sig -- MonadReader (M.Map Var (Value v)) m
  , Carrier sig m
  , EvalPrim m v (Sum (Map Const p))
  , LambdaValue m :< v
  ) => Expr p -> m (Value v)
eval = cata alg
  where
    alg :: ExprF p (m (Value v)) -> m (Value v)
    alg = \case
      Ref pos x -> do
        v <- asks (M.lookup x)
        case v of
          Nothing -> throwError $ show pos ++ ": Variable not found: " ++ show x
          Just v' -> pure v'

      Lambda _pos x body -> do
        env <- ask
        let f v = local (\_ -> M.insert x v env) body
        pure $ mkVLam @m f

      App pos f e -> do
        f' <- f
        case project (unfix f') of
          Just (VLam f'') -> e >>= f''
          _ -> throwError $ show pos ++ ": Could not apply to a non-function"

      Prim _pos p ->
        evalPrim p

----------------------------------------------------------------------

var :: Variable -> Expr p
var x = Fix (Ref dummyPos x)

lam :: Variable -> Expr p -> Expr p
lam x b = Fix (Lambda dummyPos x b)

let_ :: Variable -> Expr p -> Expr p -> Expr p
let_ x a b = Fix (App dummyPos (Fix (Lambda dummyPos x b)) a)

(!) :: Expr p -> Expr p -> Expr p
(!) f e = Fix (App dummyPos f e)

infixl 1 !
