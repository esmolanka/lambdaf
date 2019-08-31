{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE ImplicitParams      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module TypeChecker where

import Control.Monad
import Control.Effect.Lift
import Control.Effect.Pure
import Control.Effect.Error
import Control.Effect.State
import Control.Effect.Reader

import Data.Functor.Const
import Data.Functor.Foldable (cata, para, Fix (..))
import qualified Data.Set as S
import Data.Sum

import Expr
import Types
import Context (Context)
import qualified Context as Ctx
import Errors
import Position
import Utils

newtype FreshSupply = FreshSupply { getFreshName :: Int }

type TypeChecking sig =
  ( Member (State FreshSupply) sig
  , Member (Reader Context) sig
  , Member (Error TCError) sig
  )

newTyVar :: (TypeChecking sig, Carrier sig m) => Kind -> m Type
newTyVar kind = do
  name <- gets getFreshName
  modify (\s -> s { getFreshName = getFreshName s + 1 })
  return $ Fix $ TVar $ TyVar name kind

instantiate :: forall m sig. (TypeChecking sig, Carrier sig m) => TyScheme -> m Type
instantiate TyScheme{..} = do
  subst <- simultaneousSubst <$> mapM mkFreshVar tsForall
  return $ applySubst subst tsBody
  where
    mkFreshVar :: TyVar -> m (TyVar, Type)
    mkFreshVar tv = (,) <$> pure tv <*> newTyVar (tvKind tv)

generalize :: (TypeChecking sig, Carrier sig m) => Type -> m TyScheme
generalize ty = do
  freeInCtx <- asks @Context freeTyVars
  return (TyScheme (S.toList (freeTyVars ty `S.difference` freeInCtx)) ty)

----------------------------------------------------------------------
-- Unification

unifyBaseTypes :: (?pos :: Position, TypeChecking sig, Carrier sig m) => BaseType -> BaseType -> m ()
unifyBaseTypes a b =
  unless (a == b) $
    throwError (TCError ?pos (CannotUnify (Fix (T a)) (Fix (T b))))

unifyEmbeddedTypes :: (?pos :: Position, TypeChecking sig, Carrier sig m) => EType -> EType -> m ()
unifyEmbeddedTypes a b =
  unless (a == b) $
    throwError (TCError ?pos (CannotUnify (Fix (TE a)) (Fix (TE b))))

unifyVars :: (?pos :: Position, TypeChecking sig, Carrier sig m) => TyVar -> TyVar -> m TySubst
unifyVars a b = do
  unless (tvKind a == tvKind b) $
    throwError (TCError ?pos (KindMismatch (tvKind a) (tvKind b)))
  return (singletonSubst a (Fix (TVar b)))

unifyIs :: (?pos :: Position, TypeChecking sig, Carrier sig m) => TyVar -> Type -> m TySubst
unifyIs tv typ
  | tv `S.member` freeTyVars typ = throwError (TCError ?pos (InfiniteType typ))
  | otherwise = return (singletonSubst tv typ)

unify :: (?pos :: Position, TypeChecking sig, Carrier sig m) => Type -> Type -> m TySubst
unify (Fix l) (Fix r) = do
  lk <- inferKind (Fix l)
  rk <- inferKind (Fix r)
  unless (lk == rk) $
    throwError (TCError ?pos (KindMismatch lk rk))
  case (l, r) of
    (TVar x,  TVar y)  -> unifyVars x y
    (TVar x,  typ)     -> x `unifyIs` Fix typ
    (typ,     TVar y)  -> y `unifyIs` Fix typ
    (T x,     T y)     -> emptySubst <$ unifyBaseTypes x y
    (TE x,    TE y)    -> emptySubst <$ unifyEmbeddedTypes x y
    (TExpr x, TExpr y) -> unify x y

    (TPair x a,  TPair y b)  -> do
      s1 <- unify x y
      s2 <- unify (applySubst s1 a) (applySubst s1 b)
      pure $ s2 `composeSubst` s1
    (TRecord x,  TRecord y)  -> unify x y
    (TVariant x, TVariant y) -> unify x y
    (TPresent,   TPresent)   -> pure emptySubst
    (TAbsent,    TAbsent)    -> pure emptySubst
    (TArrow a f x, TArrow b g y) -> do
      s1 <- unify a b
      s2 <- unify (applySubst s1 f) (applySubst s1 g)
      let s3 = s2 `composeSubst` s1
      s4 <- unify (applySubst s3 x) (applySubst s3 y)
      pure $ s4 `composeSubst` s3

    (TRowEmpty,  TRowEmpty) -> pure emptySubst

    (TRowExtend lbl pty fty tail_, TRowExtend lbl' pty' fty' tail') -> do
      (pty'', fty'', tail'', s1) <- rewriteRow lbl lbl' pty' fty' tail'
      case getRowTail tail_ of
        Just rest | domSubst rest s1 -> throwError (TCError ?pos (RecursiveRowType (Fix (TRowExtend lbl' pty'' fty'' tail''))))
        _ -> do
          s2 <- unify (applySubst s1 pty) (applySubst s1 pty'')
          let s3 = composeSubst s2 s1
          s4 <- unify (applySubst s3 fty) (applySubst s3 fty'')
          let s5 = composeSubst s4 s3
          s6 <- unify (applySubst s5 tail_) (applySubst s5 tail'')
          return (composeSubst s6 s5)

    (TRowEmpty, TRowExtend lbl p f rest) ->
      unify
        (Fix (TRowExtend lbl (Fix TAbsent) f (Fix TRowEmpty)))
        (Fix (TRowExtend lbl p f rest))

    (TRowExtend lbl p f rest, TRowEmpty) ->
      unify
        (Fix (TRowExtend lbl p f rest))
        (Fix (TRowExtend lbl (Fix TAbsent) f (Fix TRowEmpty)))

    _ -> throwError (TCError ?pos (CannotUnify (Fix l) (Fix r)))


rewriteRow
  :: (?pos :: Position, TypeChecking sig, Carrier sig m) =>
     Label -> Label -> Type -> Type -> Type -> m (Type, Type, Type, TySubst)
rewriteRow newLbl lbl pty fty tail_ =
  if newLbl == lbl
  then return (pty, fty, tail_, emptySubst)
  else
    case tail_ of
      Fix (TVar alpha) -> do
        beta  <- newTyVar Row
        gamma <- newTyVar Star
        theta <- newTyVar Presence
        s     <- alpha `unifyIs` Fix (TRowExtend newLbl theta gamma beta)
        return (theta, gamma, applySubst s (Fix (TRowExtend lbl pty fty beta)), s)
      Fix (TRowExtend lbl' pty' fty' tail') -> do
        (pty'', fty'', tail'', s) <- rewriteRow newLbl lbl' pty' fty' tail'
        return (pty'', fty'', Fix (TRowExtend lbl pty fty tail''), s)
      Fix TRowEmpty -> do
        gamma <- newTyVar Star
        return (Fix TAbsent, gamma, Fix (TRowExtend lbl pty fty (Fix TRowEmpty)), emptySubst)
      _other ->
        error $ "Unexpected type: " ++ show tail_

----------------------------------------------------------------------
-- Type inference

inferType
  :: forall m p sig.
     ( TypeChecking sig
     , Carrier sig m
     , TypePrim (Sum (Map Const p))
     ) => Expr p -> m (TySubst, Type, Type)
inferType = para alg
  where
    alg :: ExprF p (Expr p, m (TySubst, Type, Type)) -> m (TySubst, Type, Type)
    alg = \case
      Ref pos x -> do
        mts <- asks (Ctx.lookup x 0)
        case mts of
          Nothing -> throwError (TCError pos (VariableNotFound (show x)))
          Just sigma -> do
            typ <- instantiate sigma
            eff <- newTyVar Row
            return
              ( emptySubst
              , typ
              , eff
              )

      Lambda _pos x (_, b) -> do
        tv <- newTyVar Star
        (s1, t1, eff1) <- Ctx.with x (TyScheme [] tv) b
        eff <- newTyVar Row
        return
          ( s1
          , Fix (TArrow (applySubst s1 tv) eff1 t1)
          , eff
          )

      App pos (_, f) (_, a) -> let ?pos = pos in do
        (sf, tf, eff1) <- f
        (sa, ta, eff2) <- Ctx.withSubst sf a
        tr <- newTyVar Star
        sr <- unify (applySubst sa tf) (Fix (TArrow ta eff2 tr))
        se <- unify (applySubst (sr `composeSubst` sa) eff1) (applySubst sr eff2)
        return
          ( se `composeSubst` sr `composeSubst` sa `composeSubst` sf
          , applySubst (se `composeSubst` sr) tr
          , applySubst (se `composeSubst` sr) eff2
          )

      Prim _pos c -> do
        typ <- instantiate $ typePrim c
        eff <- newTyVar Row
        return (emptySubst, typ, eff)

      Let pos x (_, e) (_, b) -> let ?pos = pos in do
        (se, te, eff1) <- e
        sf <- unify eff1 (Fix TRowEmpty)
        (sb, tb, eff2) <- Ctx.withSubst (sf `composeSubst` se) $ do
          scheme <- generalize te
          Ctx.with x scheme $ b
        return
          ( sb `composeSubst` sf `composeSubst` se
          , tb
          , eff2
          )

      -- Let pos DoBinding x (_, e) (_, b) -> let ?pos = pos in do
      --   (se, te, eff1) <- e
      --   (sb, tb, eff2) <- Ctx.withSubst se $ Ctx.with x (TyScheme [] te) $ b
      --   sf <- unify eff1 eff2
      --   return
      --     ( sb `composeSubst` sf `composeSubst` se
      --     , tb
          -- , eff2
          -- )


-- inferExprType
--   :: forall m. (MonadState FreshSupply m, MonadReader Context m, MonadError TCError m) =>
--      Expr -> m (Type, Type)
-- inferExprType expr = do
--   (se, te, fe) <- inferType expr
--   return (applySubst se te, applySubst se fe)


inferKind :: forall m sig. (?pos :: Position, TypeChecking sig, Carrier sig m) => Type -> m Kind
inferKind = cata (alg <=< sequence)
  where
    alg :: TypeF Kind -> m Kind
    alg = \case
      TVar tv              -> return (tvKind tv)
      T _                  -> return Star
      TE _                 -> return EStar
      TExpr EStar          -> return Star
      TArrow Star Row Star -> return Star
      TPair Star Star      -> return Star
      TRecord Row          -> return Star
      TVariant Row         -> return Star
      TPresent             -> return Presence
      TAbsent              -> return Presence
      TRowEmpty            -> return Row
      TRowExtend _
         Presence Star Row -> return Row
      other                -> throwError (TCError ?pos (IllKindedType other))

type InferM = ErrorC TCError (StateC FreshSupply (ReaderC Context PureC))

runInfer :: InferM a -> Either TCError a
runInfer =
  run .
  runReader Ctx.empty .
  evalState (FreshSupply 0) .
  runError

-- showType :: Expr -> IO ()
-- showType e = do
--   putStrLn ("checking expr:\n" ++ show e ++ "\n\n")
--   case runInfer (inferExprType e) of
--     Left err -> putStrLn (pp (ppError err))
--     Right (ty,eff) -> putStrLn $ pp (ppType ty) ++ "\n" ++ pp (ppType eff)
