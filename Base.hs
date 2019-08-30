{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeOperators              #-}
-- :-/
{-# LANGUAGE UndecidableInstances       #-}

module Base where

import Control.Monad.Except
import Control.Monad.Reader

import Data.Functor.Classes
import Data.Functor.Const
import Data.Functor.Foldable (Fix (..), unfix)
import qualified Data.Map as M
import Data.Sum

import Expr
import Utils

data BasePrim
  = Add
  | If
  | MkPair
  | MkDouble Double
  | MkUnit

data BaseValue e
  = VDbl Double
  | VPair e e
  | VUnit

mkVDbl :: (BaseValue :< v) => Double -> Value v
mkVDbl x = Fix . inject $ VDbl x

mkVPair :: (BaseValue :< v) => Value v -> Value v -> Value v
mkVPair a b = Fix . inject $ VPair a b

mkVUnit :: (BaseValue :< v) => Value v
mkVUnit = Fix . inject $ VUnit

instance Show1 BaseValue where
  liftShowsPrec sp _sl _n = \case
    VDbl x    -> showString "#" . shows x
    VPair a b -> showString "(" . sp 0 a . showString " ** " . sp 0 b . showString ")"
    VUnit     -> showString "Unit"

instance ( MonadError String m
         , LambdaValue m :< v
         , BaseValue :< v
         ) => EvalPrim m v (Const BasePrim) where
  evalPrim = \case
      Const Add ->
        pure $ mkVLam @m $ \x ->
        pure $ mkVLam @m $ \y ->
          case projBase x of
            Just (VDbl x') ->
              case projBase y of
                Just (VDbl y') -> pure $ mkVDbl (x' + y')
                _ -> throwError "RHS is not a double!"
            _ -> throwError "LHS is not a double!"

      Const If ->
        pure $ mkVLam @m $ \c ->
        pure $ mkVLam @m $ \t ->
        pure $ mkVLam @m $ \f ->
         case projBase c of
           Just (VDbl c')
             | c' > 0    -> pure t
             | otherwise -> pure f
           _ -> throwError "Condition is not a double!"

      Const MkPair ->
        pure $ mkVLam @m $ \a ->
        pure $ mkVLam @m $ \b ->
          pure (mkVPair a b)

      Const (MkDouble n) ->
        pure $ mkVDbl n

      Const MkUnit ->
        pure $ mkVUnit
    where
      projBase = project @BaseValue . unfix

----------------------------------------------------------------------

newtype Eval a = Eval {uneval :: ExceptT String (Reader (M.Map Var (Value '[LambdaValue Eval, BaseValue]))) a}
  deriving ( Functor, Applicative, Monad
           , MonadReader (M.Map Var (Value '[LambdaValue Eval, BaseValue]))
           , MonadError String
           )

runEval :: Eval a -> Either String a
runEval k = runReader (runExceptT (uneval k)) M.empty

eval' :: Expr '[BasePrim] -> Eval (Value '[LambdaValue Eval, BaseValue])
eval' a = eval a

----------------------------------------------------------------------

prim :: (BasePrim :<< p) => BasePrim -> Expr p
prim p = Fix (Prim (inject' p))

lit :: (BasePrim :<< p) => Double -> Expr p
lit n = prim (MkDouble n)

(**) :: (BasePrim :<< p) => Expr p -> Expr p -> Expr p
(**) a b = prim MkPair ! a ! b

infixr 3 **
