{-# LANGUAGE DeriveFunctor    #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase       #-}

module Expr where

import Control.Monad.Except
import Control.Monad.Reader

import Data.Functor.Foldable (Fix (..), cata)
import Data.Functor.Identity
import qualified Data.Map as M

type Var = Int

data Prim p
  = Add
  | If
  | MkPair
  | MkUnit
  | Ext p

data ExprF p e
  = Var Var
  | Lam Var e
  | App e e
  | Lit Double
  | Prim (Prim p)
    deriving (Functor)

type Expr p = Fix (ExprF p)

type EvalT v m = ExceptT String (ReaderT (M.Map Var (Value m v)) m)
type EvalM v = EvalT v Identity

data Value m v
  = VLam (Value m v -> EvalT v m (Value m v))
  | VDbl Double
  | VPair (Value m v) (Value m v)
  | VUnit
  | VExt v

instance Show v => Show (Value m v) where
  showsPrec _ = \case
    VLam _ -> showString "VLam"
    VDbl x -> showString "[" . shows x . showString "]"
    VPair a b -> showString "(" . shows a . showString " ** " . shows b . showString ")"
    VUnit -> showString "()"
    VExt v -> showString "{" . shows v . showString "}"

eval :: (Monad m) => (p -> EvalT v m (Value m v)) -> Expr p -> EvalT v m (Value m v)
eval evalPrim = cata $ \case
  Var x -> do
    v <- asks (M.lookup x)
    case v of
      Nothing -> throwError $ "Variable not found: " ++ show x
      Just v' -> pure v'

  Lam x body -> do
    env <- ask
    let f v = local (\_ -> M.insert x v env) body
    pure $ VLam f

  App f e -> do
    f' <- f
    case f' of
      VLam f'' -> e >>= f''
      _ -> throwError "Could not apply to a non-function"

  Lit x ->
    pure (VDbl x)

  Prim Add ->
    pure $ VLam $ \x -> pure $ VLam $ \y ->
      case x of
        VDbl x' ->
          case y of
            VDbl y' -> pure $ VDbl (x' + y')
            _ -> throwError "RHS is not a double!"
        _ -> throwError "LHS is not a double!"

  Prim If ->
    pure $ VLam $ \c -> pure $ VLam $ \t -> pure $ VLam $ \f ->
      case c of
        VDbl c' | c' > 0    -> pure t
                | otherwise -> pure f
        _ -> throwError "Condition is not a double!"

  Prim MkPair ->
    pure $ VLam $ \a -> pure $ VLam $ \b -> pure (VPair a b)

  Prim MkUnit ->
    pure VUnit

  Prim (Ext eprim) ->
    evalPrim eprim

runEval :: EvalM v a -> Either String a
runEval k = runReader (runExceptT k) M.empty

runEvalT :: EvalT v m a -> m (Either String a)
runEvalT k = runReaderT (runExceptT k) M.empty
