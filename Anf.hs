{-# LANGUAGE DeriveFunctor    #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase       #-}

module Anf where

import Prelude hiding ((**))

import Control.Monad.Except
import Control.Monad.State

import Data.Functor.Foldable (Fix (..))
import qualified Data.Set as S

import Expr

type AnfM = EvalT ValueAnf (State EVar)

data ValueAnf = VAnf EExpr | VStore EVar EExpr AnfValue deriving (Show)
data PrimAnf = Const | EPrim EPrim | ELoop deriving (Show)

type AnfPrim = Prim PrimAnf
type AnfValue = Value (State EVar) ValueAnf

evalPrim :: PrimAnf -> AnfM AnfValue
evalPrim = \case
  Const ->
    pure $ VLam $ \x ->
      case x of
        VDbl x' -> pure $ VExt $ VAnf (EIn (ELit x'))
        _ -> throwError "Value is not a double!"

  EPrim eprim -> do
    pure $ VLam $ \x -> pure $ VLam $ \y ->
      case x of
        VExt (VAnf x') ->
          case y of
            VExt (VAnf y') -> do
              anf <- apply eprim x' y'
              pure (VExt (VAnf anf))
            _ -> throwError "RHS is not an ANF!"
        _ -> throwError "LHS is not an ANF!"

  ELoop ->
    pure $ VLam $ \f ->
      case f of
        VLam f' -> do
          stateVar <- fresh
          res <- f' (VExt (VAnf (EIntro stateVar (EIn (ERef stateVar)))))
          let store :: AnfValue -> AnfM AnfValue
              store = \case
                (VExt (VStore x s r))     -> VExt . VStore x s <$> store r
                (VPair (VExt (VAnf s)) r) -> pure (VExt (VStore stateVar s r))
                _                         -> throwError $ "Loop result is not a VStore or VPair"

              flatten :: AnfValue -> AnfM EExpr
              flatten = \case
                VExt (VStore x s r) -> apply (EStore x) (EIntro x s) =<< flatten r
                VExt (VAnf x)       -> pure x
                _                   -> throwError "Can't flatten yet"

          (store res >>= flatten >>= pure . VExt . VAnf) `mplus` store res

        _ -> throwError "Loop body is not a function!"

----------------------------------------------------------------------
-- ANF

type EVar = Int

data EPrim = EAdd | EStore EVar
  deriving (Show)

data EExpr
  = ELet   EVar EPrim [EValue] EExpr
  | EIntro EVar EExpr
  | EIn    EValue
    deriving (Show)

data EValue
  = ERef EVar
  | ELit Double
    deriving (Show)

fresh :: AnfM EVar
fresh = do
  x <- get
  modify succ
  return x

apply :: EPrim -> EExpr -> EExpr -> AnfM EExpr
apply newprim lhs rhs = do
  var <- fresh
  pure (go var S.empty lhs)
  where
    go :: EVar -> S.Set EVar -> EExpr -> EExpr
    go x used = \case
      ELet ref prim args rest
        | S.member ref used -> go x used rest
        | otherwise -> ELet ref prim args (go x (S.insert ref used) rest)
      EIntro ref rest
        | S.member ref used -> go x used rest
        | otherwise -> EIntro ref (go x (S.insert ref used) rest)
      EIn lhsval ->
        go2 lhsval x used rhs

    go2 :: EValue -> EVar -> S.Set EVar -> EExpr -> EExpr
    go2 lhsval x used = \case
      ELet ref prim args rest
        | S.member ref used  -> go2 lhsval x used rest
        | otherwise -> ELet ref prim args (go2 lhsval x (S.insert ref used) rest)
      EIntro ref rest
        | S.member ref used  -> go2 lhsval x used rest
        | otherwise -> EIntro ref (go2 lhsval x (S.insert ref used) rest)
      EIn rhsval ->
        ELet x newprim [lhsval, rhsval] (EIn (ERef x))


----------------------------------------------------------------------
-- Example

eval' :: AnfExpr -> AnfValue
eval' = either error id . flip evalState 100 . runEvalT . eval evalPrim


type AnfExpr = Expr PrimAnf

var :: Var -> AnfExpr
var x = Fix (Var x)

lit :: Double -> AnfExpr
lit n = Fix (Lit n)

(**) :: AnfExpr -> AnfExpr -> AnfExpr
(**) a b = prim MkPair ! a ! b

infixr 3 **

lam :: Var -> AnfExpr -> AnfExpr
lam x b = Fix (Lam x b)

let_ :: Var -> AnfExpr -> AnfExpr -> AnfExpr
let_ x a b = Fix (App (Fix (Lam x b)) a)

(!) :: AnfExpr -> AnfExpr -> AnfExpr
(!) f e = Fix (App f e)

infixl 1 !

prim :: Prim PrimAnf -> AnfExpr
prim p = Fix (Prim p)

cnst :: AnfExpr -> AnfExpr
cnst x = prim (Ext Const) ! x

eadd :: AnfExpr -> AnfExpr -> AnfExpr
eadd x y = prim (Ext (EPrim EAdd)) ! x ! y

loop :: AnfExpr -> AnfExpr
loop x = prim (Ext ELoop) ! x

----------------------------------------------------------------------

test1 :: AnfExpr
test1 =
  let_ 0 (lit (-3.14))
  $ let_ 1 (prim Add ! lit 10 ! var 0)
  $ let_ 2 (cnst (var 1))
  $ let_ 3 (var 2 `eadd` var 2)
  $ var 2 `eadd` (prim If ! var 0 ! var 2 ! var 3)

test2 :: AnfExpr
test2 =
  loop $ lam 1 $
    loop $ lam 2 $
      var 1 **
      var 2 **
      cnst (lit 30)
