{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MonoLocalBinds             #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
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
import qualified Data.Text as T
import Data.Text.Prettyprint.Doc as PP
import Data.Void

import Utils
import Syntax.Position

newtype Variable = Variable T.Text
  deriving (Eq, Ord, Show)

type Expr (p :: [*]) = Fix (ExprF p)
type Value (l :: [* -> *]) = Fix (Sum l)

data ExprF (p :: [*]) e
  = Ref    Position Variable
  | Lambda Position Variable e
  | App    Position e e
  | Let    Position Variable e e
  | Prim   Position (Sum' p)
    deriving (Functor)

data LambdaValue m e
  = VLam (e -> m e)

mkVLam :: forall m v. (LambdaValue m :< v) => (Value v -> m (Value v)) -> Value v
mkVLam x = Fix . inject $ VLam x

instance Show1 (LambdaValue m) where
  liftShowsPrec _sp _sl _n = \case
    VLam _ -> showString "<Lambda>"

instance Pretty1 (LambdaValue m) where
  liftPretty _pp = \case
    VLam _ -> pretty "<Lambda>"

evalError :: (Member (Error String) sig, Carrier sig m) => String -> m a
evalError = throwError

class EvalPrim m v (p :: * -> *) where
  evalPrim :: p Void -> m (Value v)

instance (Apply (EvalPrim m v) ps) => EvalPrim m v (Sum ps) where
  evalPrim = apply @(EvalPrim m v) evalPrim

eval :: forall m sig (p :: [*]) (v :: [* -> *]).
  ( Member (Error String) sig
  , Member (Reader (M.Map Variable (Value v))) sig
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

      Let _pos x e body -> do
        v <- e
        local (M.insert x v) body

      Prim _pos p ->
        evalPrim p

----------------------------------------------------------------------

var :: Int -> Expr p
var x = Fix (Ref dummyPos (Variable (T.pack (show x))))

lam :: Int -> Expr p -> Expr p
lam x b = Fix (Lambda dummyPos (Variable (T.pack (show x))) b)

let_ :: Int -> Expr p -> Expr p -> Expr p
let_ x a b = Fix (Let dummyPos (Variable (T.pack (show x))) a b)

(!) :: Expr p -> Expr p -> Expr p
(!) f e = Fix (App dummyPos f e)

infixl 1 !
