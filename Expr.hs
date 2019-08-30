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

import Control.Monad.Except
import Control.Monad.Reader

import Data.Functor.Classes
import Data.Functor.Const
import Data.Functor.Foldable (Fix (..), unfix, cata)
import qualified Data.Map as M
import Data.Proxy
import Data.Sum
import Data.Void

import Utils

type Var = Int

type Expr (p :: [*]) = Fix (ExprF p)
type Value (l :: [* -> *]) = Fix (Sum l)

data ExprF (p :: [*]) e
  = Var Var
  | Lam Var e
  | App e e
  | Lit Double
  | Prim (Sum' p)
    deriving (Functor)

data BasePrim
  = Add
  | If
  | MkPair
  | MkUnit

data BaseValue m e
  = VLam (e -> m e)
  | VDbl Double
  | VPair e e
  | VUnit

mkVLam :: forall proxy m v. (BaseValue m :< v) => proxy m -> (Value v -> m (Value v)) -> Value v
mkVLam _ x = Fix . inject $ VLam @m x

mkVDbl :: forall proxy m v. (BaseValue m :< v) => proxy m -> Double -> Value v
mkVDbl _ x = Fix . inject $ VDbl @m x

mkVPair :: forall proxy m v. (BaseValue m :< v) => proxy m -> Value v -> Value v -> Value v
mkVPair _ a b = Fix . inject $ VPair @m a b

mkVUnit :: forall proxy m v. (BaseValue m :< v) => proxy m -> Value v
mkVUnit _ = Fix . inject $ VUnit @m

instance Show1 (BaseValue m) where
  liftShowsPrec sp _sl _n = \case
    VLam _    -> showString "<Lambda>"
    VDbl x    -> showString "#" . shows x
    VPair a b -> showString "(" . sp 0 a . showString " ** " . sp 0 b . showString ")"
    VUnit     -> showString "Unit"

class EvalPrim m v (p :: * -> *) where
  evalPrim :: p Void -> m (Value v)

instance (Apply (EvalPrim m v) ps) => EvalPrim m v (Sum ps) where
  evalPrim = apply @(EvalPrim m v) evalPrim

instance (MonadError String m, BaseValue m :< v) => EvalPrim m v (Const BasePrim) where
  evalPrim = \case
      Const Add ->
        pure $ mkVLam (Proxy @m) $ \x ->
        pure $ mkVLam (Proxy @m) $ \y ->
          case proj x of
            Just (VDbl x') ->
              case proj y of
                Just (VDbl y') -> pure $ mkVDbl (Proxy @m) (x' + y')
                _ -> throwError "RHS is not a double!"
            _ -> throwError "LHS is not a double!"

      Const If ->
        pure $ mkVLam (Proxy @m) $ \c ->
        pure $ mkVLam (Proxy @m) $ \t ->
        pure $ mkVLam (Proxy @m) $ \f ->
         case proj c of
           Just (VDbl c')
             | c' > 0    -> pure t
             | otherwise -> pure f
           _ -> throwError "Condition is not a double!"

      Const MkPair ->
        pure $ mkVLam (Proxy @m) $ \a ->
        pure $ mkVLam (Proxy @m) $ \b ->
          pure (mkVPair (Proxy @m) a b)

      Const MkUnit ->
        pure $ mkVUnit (Proxy @m)
    where
      proj = project @(BaseValue m) . unfix

eval :: forall m (p :: [*]) (v :: [* -> *]).
  ( MonadError String m
  , MonadReader (M.Map Var (Value v)) m
  , EvalPrim m v (Sum (Map Const p))
  , BasePrim :<< p
  , BaseValue m :< v
  ) => Expr p -> m (Value v)
eval = cata alg
  where
    alg :: ExprF p (m (Value v)) -> m (Value v)
    alg = \case
      Var x -> do
        v <- asks (M.lookup x)
        case v of
          Nothing -> throwError $ "Variable not found: " ++ show x
          Just v' -> pure v'

      Lam x body -> do
        env <- ask
        let f v = local (\_ -> M.insert x v env) body
        pure $ mkVLam (Proxy @m) f

      App f e -> do
        f' <- f
        case project (unfix f') of
          Just (VLam f'') -> e >>= f''
          _ -> throwError "Could not apply to a non-function"

      Lit x ->
        pure $ mkVDbl (Proxy @m) x

      Prim p ->
        evalPrim p

----------------------------------------------------------------------

newtype Eval a = Eval {uneval :: ExceptT String (Reader (M.Map Var (Value '[BaseValue Eval]))) a}
  deriving ( Functor, Applicative, Monad
           , MonadReader (M.Map Var (Value '[BaseValue Eval]))
           , MonadError String
           )

runEval :: Eval a -> Either String a
runEval k = runReader (runExceptT (uneval k)) M.empty

eval' :: Expr '[BasePrim] -> Eval (Value '[BaseValue Eval])
eval' a = eval a

var :: Var -> Expr p
var x = Fix (Var x)

lit :: Double -> Expr p
lit n = Fix (Lit n)

lam :: Var -> Expr p -> Expr p
lam x b = Fix (Lam x b)

let_ :: Var -> Expr p -> Expr p -> Expr p
let_ x a b = Fix (App (Fix (Lam x b)) a)

(!) :: Expr p -> Expr p -> Expr p
(!) f e = Fix (App f e)

infixl 1 !

prim :: (BasePrim :<< p) => BasePrim -> Expr p
prim p = Fix (Prim (inject' p))

(**) :: (BasePrim :<< p) => Expr p -> Expr p -> Expr p
(**) a b = prim MkPair ! a ! b

infixr 3 **
