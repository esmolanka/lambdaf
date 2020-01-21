{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MonoLocalBinds             #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}

module TypeChecker (runInfer, inferExprType) where

import Control.Monad
import Control.Effect.State
import Control.Effect.Error
import Control.Effect.Reader
import Control.Effect.Writer
import Control.Effect.Pure
import Control.Effect.Carrier

import Data.Foldable (toList, fold)
import Data.Functor.Foldable (Fix (..), cata)
import Data.Maybe
import Data.Monoid (All(..), Any(..))
import Data.Sequence (Seq(..))
import qualified Data.Sequence as Seq
import Data.Sum
import Data.Text.Prettyprint.Doc as PP

-- import Debug.Trace

import Syntax.Position
import Errors
import Expr
import Types
import Utils
import Pretty

trace :: String -> a -> a
trace = flip const

isMono :: Type -> Bool
isMono = getAll . cata alg
  where
    alg = \case
      TForall _ _ -> All False
      other -> fold other

isForall :: Type -> Bool
isForall = \case
  Fix (TForall _ _) -> True
  _other -> False

data CtxMember
  = CtxVar    TVar
  | CtxAssump Variable Type
  | CtxMeta   MetaVar
  | CtxSolved MetaVar Type
  | CtxMarker MetaVar
  deriving (Eq, Ord, Show)

newtype Ctx = Ctx (Seq CtxMember)
  deriving (Eq, Show, Semigroup, Monoid)

ppCtx :: Ctx -> Doc ann
ppCtx (Ctx elems) = indent 2 . vsep . map ppMember . toList $ elems
  where
    ppMember :: CtxMember -> Doc ann
    ppMember = \case
      CtxVar tv       -> "skolem" <+> ppTyVar tv
      CtxAssump v ty  -> "assump" <+> ppVariable v <+> ":" <+> ppType ty
      CtxMeta ev      -> "unsolv" <+> ppMetaVar ev
      CtxSolved ev ty -> "solved" <+> ppMetaVar ev <+> "=" <+> ppType ty
      CtxMarker ev    -> "marker" <+> "▸" <> ppMetaVar ev

(▸) :: Ctx -> CtxMember -> Ctx
(Ctx ctx) ▸ mem = Ctx (ctx :|> mem)

ctxHole :: CtxMember -> Ctx -> Maybe (Ctx, Ctx)
ctxHole mem (Ctx ctx) =
  let (front, rear) = Seq.breakr (== mem) ctx
  in case rear of
       Empty -> Nothing
       rear' :|> _ -> Just (Ctx rear', Ctx front)

ctxHoles :: CtxMember -> CtxMember -> Ctx -> Maybe (Ctx, Ctx, Ctx)
ctxHoles x y ctx = do
  (a, rest) <- ctxHole x ctx
  (b, c)    <- ctxHole y rest
  return (a, b, c)

ctxAssump :: Ctx -> Variable -> Maybe Type
ctxAssump (Ctx ctx) x = go ctx
  where
    go = \case
      Empty -> Nothing
      _    :|> CtxAssump y t | x == y -> Just t
      rest :|> _ -> go rest

ctxSolution :: Ctx -> MetaVar -> Maybe Type
ctxSolution (Ctx ctx) x = go ctx
  where
    go = \case
      Empty -> Nothing
      _    :|> CtxSolved y t | x == y -> Just t
      _    :|> CtxMeta   y   | x == y -> Nothing
      rest :|> _ -> go rest

ctxHasSkolem :: Ctx -> TVar -> Bool
ctxHasSkolem (Ctx ctx) v =
  CtxVar v `elem` ctx

ctxHasMeta :: Ctx -> MetaVar -> Bool
ctxHasMeta (Ctx ctx) x = go ctx
  where
    go = \case
      Empty -> False
      _    :|> CtxSolved y _ | x == y -> True
      _    :|> CtxMeta   y   | x == y -> True
      rest :|> _ -> go rest

ctxDrop :: CtxMember -> Ctx -> Ctx
ctxDrop m (Ctx ctx) =
  Ctx $ Seq.dropWhileR (== m) $ Seq.dropWhileR (/= m) ctx

ctxUnsolved :: Ctx -> ([TVar], Ctx)
ctxUnsolved (Ctx ctx) =
  ( flip mapMaybe (toList ctx) $ \case
      CtxMeta (MetaVar n k) -> Just (TVar n k)
      _ -> Nothing
  , Ctx $ flip fmap ctx $ \case
      CtxMeta v@(MetaVar n k) -> CtxSolved v (Fix (TRef (TVar n k)))
      other -> other
  )

----------------------------------------------------------------------

(⊢) :: Ctx -> Type -> Either Reason ()
(⊢) ctx0 ty = run $ runReader ctx0 $ runError (cata alg ty)
  where
    alg :: (Member (Error Reason) sig, Member (Reader Ctx) sig, Carrier sig m) =>
           TypeF (m ()) -> m ()
    alg t = do
      ctx <- ask
      case t of
        TRef v ->
          unless (ctxHasSkolem ctx v) $
            throwError $ TypeVariableNotFound v
        TMeta v ->
          unless (ctxHasMeta ctx v) $
            throwError $ OtherError $ "unbound meta variable ‘" ++ show v ++ "’"
        TForall v b ->
          local (▸ CtxVar v) b
        other -> sequence_ other

freeMetaIn :: MetaVar -> Type -> Bool
freeMetaIn x = getAny . cata alg
  where
    alg :: TypeF Any -> Any
    alg = \case
      TMeta v | x == v -> Any True
      other -> fold other

applySolutions :: Ctx -> Type -> Type
applySolutions ctx = cata alg
  where
    alg :: TypeF Type -> Type
    alg = \case
      TMeta v -> maybe (Fix (TMeta v)) (applySolutions ctx) (ctxSolution ctx v)
      other   -> Fix other

subst :: (TVar, Type) -> Type -> Type
subst (v, s) = cata alg
  where
    alg :: TypeF Type -> Type
    alg = \case
      TRef v' | v == v' -> s
      other -> Fix other

----------------------------------------------------------------------

type TypeChecking sig =
  ( Member (State CheckState) sig
  , Member (Error TCError) sig
  , Effect sig
  )

data CheckState = CheckState
  { checkCtx :: Ctx
  , checkNextEVar :: Int
  } deriving (Eq, Show)

defCheckState :: CheckState
defCheckState = CheckState mempty 1

getCtx :: (TypeChecking sig, Carrier sig m) => m Ctx
getCtx = gets checkCtx

putCtx :: (TypeChecking sig, Carrier sig m) => Ctx -> m ()
putCtx ctx = get >>= \s -> put s { checkCtx = ctx }

modifyCtx :: (TypeChecking sig, Carrier sig m) => (Ctx -> Ctx) -> m ()
modifyCtx f = putCtx . f =<< getCtx

freshMeta :: (TypeChecking sig, Carrier sig m) => Kind -> m MetaVar
freshMeta k = do
  n <- gets checkNextEVar
  modify (\s -> s { checkNextEVar = checkNextEVar s + 1 })
  pure $ MetaVar n k

(≤) :: (TypeChecking sig, Carrier sig m) => Type -> Type -> m ()
(≤) (Fix typeA) (Fix typeB) =
  getCtx >>= \ctx ->
    trace (render $ vsep [ "tySub: " <+> ppType (Fix typeA) <+> "<" <+> ppType (Fix typeB), ppCtx ctx ]) $
      typeA ≤· typeB
  where
    (≤·) :: (TypeChecking sig, Carrier sig m) => TypeF Type -> TypeF Type -> m ()

    TForall v a ≤· b | not (isForall (Fix b)) = do
      ma <- freshMeta (tvKind v)
      let a' = subst (v, Fix (TMeta ma)) a
      modifyCtx (\c -> c ▸ CtxMarker ma ▸ CtxMeta ma)
      a' ≤ Fix b
      modifyCtx (ctxDrop (CtxMarker ma))

    a ≤· TForall v b = do
      modifyCtx (▸ CtxVar v)
      Fix a ≤ b
      modifyCtx (ctxDrop (CtxVar v))

    TRef a   ≤· TRef b  | a == b = return ()
    TMeta a  ≤· TMeta b | a == b = return ()
    TCtor a  ≤· TCtor b | a == b = return ()

    TApp f a ≤· TApp g b = do
      case filter isMono [f, g, a, b] of
        (t : _) -> throwError $ TCError dummyPos $ ImpredicativePolymoprhism t
        []      -> pure ()
      f ≤ g
      getCtx >>= \ctx -> applySolutions ctx a ≤ applySolutions ctx b

    TArrow a b ≤· TArrow a' b' = do
      a' ≤ a -- contravariant
      getCtx >>= \ctx -> applySolutions ctx b ≤ applySolutions ctx b'

    TMeta ma ≤· a | not (ma `freeMetaIn` Fix a) = instantiate Rigid ma (Fix a)
    a ≤· TMeta ma | not (ma `freeMetaIn` Fix a) = instantiate Flex  ma (Fix a)

    T a  ≤· T b  | a == b = pure ()
    TE a ≤· TE b | a == b = pure ()
    TExpr x ≤· TExpr y = x ≤ y
    TPair a b ≤· TPair a' b' = do
      a ≤ a'
      getCtx >>= \ctx -> applySolutions ctx b ≤ applySolutions ctx b'

    TRecord a ≤· TRecord a' = a ≤ a'
    TVariant a ≤· TVariant a' = a ≤ a'

    TPresent ≤· TPresent = pure ()
    TAbsent ≤· TAbsent = pure ()

    TRowEmpty ≤· TRowEmpty = pure ()
    TRowExtend lbl pty fty tail_ ≤· TRowExtend lbl' pty' fty' tail' = do
      (pty'', fty'', tail'') <- rewriteRow dummyPos lbl lbl' pty' fty' tail'
      getCtx >>= \ctx -> applySolutions ctx pty   ≤ applySolutions ctx pty''
      getCtx >>= \ctx -> applySolutions ctx fty   ≤ applySolutions ctx fty''
      getCtx >>= \ctx -> applySolutions ctx tail_ ≤ applySolutions ctx tail''

    TRowEmpty ≤· TRowExtend lbl p f rest =
      (Fix (TRowExtend lbl (Fix TAbsent) f (Fix TRowEmpty))) ≤ (Fix (TRowExtend lbl p f rest))

    TRowExtend lbl p f rest ≤· TRowEmpty =
      (Fix (TRowExtend lbl p f rest)) ≤ (Fix (TRowExtend lbl (Fix TAbsent) f (Fix TRowEmpty)))

    a ≤· b = throwError $ TCError dummyPos $ CannotUnify (Fix b) (Fix a)

rewriteRow
  :: (TypeChecking sig, Carrier sig m) =>
     Position -> Label -> Label -> Type -> Type -> Type -> m (Type, Type, Type)
rewriteRow pos newLbl lbl pty fty tail_ =
  if newLbl == lbl
  then return (pty, fty, tail_)
  else
    case tail_ of
      Fix (TMeta alpha) -> do
        beta  <- freshMeta Row
        gamma <- freshMeta Star
        theta <- freshMeta Presence
        ctx1 <- getCtx
        case ctxHole (CtxMeta alpha) ctx1 of
          Just (l, r) -> do
            putCtx $ l
              ▸ CtxMeta beta
              ▸ CtxMeta gamma
              ▸ CtxMeta theta
              ▸ CtxSolved alpha (Fix (TRowExtend newLbl (Fix (TMeta theta)) (Fix (TMeta gamma)) (Fix (TMeta beta))))
              <> r
            getCtx >>= \ctx2 -> pure (Fix (TMeta theta), Fix (TMeta gamma), Fix (TRowExtend lbl (applySolutions ctx2 pty) (applySolutions ctx2 fty) (Fix (TMeta beta))))
          Nothing -> error "cannot instantiate var"
      Fix (TRowExtend lbl' pty' fty' tail') -> do
        (pty'', fty'', tail'') <- rewriteRow pos newLbl lbl' pty' fty' tail'
        getCtx >>= \ctx -> pure (pty'', fty'', Fix (TRowExtend lbl (applySolutions ctx pty) (applySolutions ctx fty) tail''))
      Fix TRowEmpty -> do
        gamma <- freshMeta Star
        pure (Fix TAbsent, Fix (TMeta gamma), Fix (TRowExtend lbl pty fty (Fix TRowEmpty)))
      _other ->
        error $ "Unexpected type: " ++ show tail_

data Direction = Flex | Rigid deriving (Eq, Ord, Show)

opposite :: Direction -> Direction
opposite = \case
  Flex -> Rigid
  Rigid -> Flex

instantiate :: (TypeChecking sig, Carrier sig m) => Direction -> MetaVar -> Type -> m ()
instantiate dir ma t = getCtx >>= go
  where
  -- Inst*Solve
  go ctx | True <- isMono t, Just (l, r) <- ctxHole (CtxMeta ma) ctx, Right{} <- l ⊢ t =
    putCtx $ l ▸ CtxSolved ma t <> r

  -- Inst*Reach
  go ctx | Fix (TMeta ma') <- t, Just (l, m, r) <- ctxHoles (CtxMeta ma) (CtxMeta ma') ctx =
    putCtx $ l ▸ CtxMeta ma <> m ▸ CtxSolved ma' (Fix (TMeta ma)) <> r

  -- Inst*Arr
  go ctx | Just (l, r) <- ctxHole (CtxMeta ma) ctx, Fix (TArrow a b) <- t = do
    ma1 <- freshMeta Star
    ma2 <- freshMeta Star
    putCtx $ l ▸ CtxMeta ma2 ▸ CtxMeta ma2 ▸ CtxMeta ma1 ▸ CtxSolved ma (Fix (TArrow (Fix (TMeta ma1)) (Fix (TMeta ma2)))) <> r
    instantiate (opposite dir) ma1 a
    getCtx >>= \ctx' -> instantiate dir ma2 (applySolutions ctx' b)

  -- Inst*App
  go ctx | Just (l, r) <- ctxHole (CtxMeta ma) ctx, Fix (TPair a b) <- t = do
    ma1 <- freshMeta Star
    ma2 <- freshMeta Star
    putCtx $ l ▸ CtxMeta ma2 ▸ CtxMeta ma1 ▸ CtxSolved ma (Fix (TPair (Fix (TMeta ma1)) (Fix (TMeta ma2)))) <> r
    instantiate dir ma1 a
    ctx' <- getCtx
    instantiate dir ma2 (applySolutions ctx' b)

  -- InstLAllR
  go ctx | Fix (TForall b s) <- t, Rigid <- dir = do
    putCtx $ ctx ▸ CtxVar b
    instantiate dir ma s
    modifyCtx (ctxDrop (CtxVar b))

  -- InstRAllL
  go ctx | Fix (TForall b s) <- t, Flex <- dir = do
    ma' <- freshMeta (tvKind b)
    putCtx $ ctx ▸ CtxMarker ma' ▸ CtxMeta ma'
    instantiate dir ma (subst (b, Fix (TMeta ma')) s)
    modifyCtx (ctxDrop (CtxMarker ma'))

  -- InstOther
  go ctx | Just (l, r) <- ctxHole (CtxMeta ma) ctx, Fix t' <- t = do
    (tasks :: [(MetaVar, Type)], t'') <- runWriter $ forM t' $ \a -> do
      k <- inferKind dummyPos a
      ma' <- freshMeta k
      tell [(ma', a)]
      return (Fix (TMeta ma'))
    putCtx $ foldl (▸) l (map (CtxMeta . fst) tasks) ▸ CtxSolved ma (Fix t'') <> r
    forM_ tasks $ \(mv, a) ->
      getCtx >>= \ctx' -> instantiate dir mv (applySolutions ctx' a)

  go _ = error $ "internal error: failed to instantiate " ++ show ma ++ " to " ++ show t

----------------------------------------------------------------------

check :: (TypeChecking sig, Carrier sig m, TypePrim (Sum (Map Const p))) => Expr p -> Type -> m ()
check e (Fix (TForall v a)) = do
  modifyCtx (▸ CtxVar v)
  check e a
  modifyCtx (ctxDrop (CtxVar v))

check (Fix (Lambda _ x e)) (Fix (TArrow a b)) = do
  modifyCtx (▸ CtxAssump x a)
  check e b
  modifyCtx (ctxDrop (CtxAssump x a))

check e b = do
  a <- infer e
  getCtx >>= \ctx -> applySolutions ctx a ≤ applySolutions ctx b

----------------------------------------------------------------------

infer :: (TypeChecking sig, Carrier sig m, TypePrim (Sum (Map Const p))) => Expr p -> m Type
infer (Fix (Ref _ x)) = do
  ctx <- getCtx
  case ctxAssump ctx x of
    Nothing -> throwError $ TCError dummyPos $ VariableNotFound x
    Just t  -> return t

infer (Fix (Annot _ e t)) = do
  ctx <- getCtx
  case ctx ⊢ t of
    Left reason -> throwError $ TCError dummyPos $ reason
    Right ()    -> check e t >> return t

infer (Fix (Lambda _ x e)) = do
  ma  <- freshMeta Star
  me  <- freshMeta Row
  ma' <- freshMeta Star
  modifyCtx $ \c -> c ▸ CtxMarker ma ▸ CtxMeta ma ▸ CtxMeta me ▸ CtxMeta ma' ▸ CtxAssump x (Fix (TMeta ma))
  check e (Fix (TMeta ma'))
  ctx <- getCtx
  case ctxHole (CtxMarker ma) ctx of
    Just (l, r) -> do
      let tau = applySolutions r (Fix (TArrow (Fix (TMeta ma)) (Fix (TMeta ma'))))
      putCtx l
      let (vars, r') = ctxUnsolved r
      return (foldr ((Fix .) . TForall) (applySolutions r' tau) vars)
    Nothing -> error "internal error: could not find marker"

infer (Fix (App _ e1 e2)) = do
  a <- infer e1
  ctx <- getCtx
  inferApp (applySolutions ctx a) e2

infer (Fix (Let _ x e1 e2)) = do
  ma <- freshMeta Star
  mb <- freshMeta Star
  modifyCtx $ \c -> c ▸ CtxMarker ma ▸ CtxMeta ma ▸ CtxMeta mb ▸ CtxAssump x (Fix (TMeta ma))
  check e1 (Fix (TMeta ma))
  check e2 (Fix (TMeta mb))
  return (Fix (TMeta mb))

infer (Fix (Prim _ c)) =
  pure (toType (typePrim c))

----------------------------------------------------------------------

inferApp :: (TypeChecking sig, Carrier sig m, TypePrim (Sum (Map Const p))) => Type -> Expr p -> m Type
inferApp (Fix (TForall v a)) e = do
  ma <- freshMeta (tvKind v)
  modifyCtx (▸ CtxMeta ma)
  inferApp (subst (v, Fix (TMeta ma)) a) e

inferApp (Fix (TMeta ma)) e = do
  ma1 <- freshMeta Star
  ma2 <- freshMeta Star
  ctx <- getCtx
  let Just (l, r) = ctxHole (CtxMeta ma) ctx
  putCtx $ l ▸ CtxMeta ma2 ▸ CtxMeta ma1 ▸ CtxSolved ma (Fix (TArrow (Fix (TMeta ma1)) (Fix (TMeta ma2)))) <> r
  check e (Fix (TMeta ma1))
  return (Fix (TMeta ma2))

inferApp (Fix (TArrow a c)) e = do
  check e a
  return c

inferApp t _e =
  throwError $ TCError dummyPos $
    OtherError $ "cannot apply to expression of type " ++ show (ppType t)

----------------------------------------------------------------------

inferKind :: forall m sig. (TypeChecking sig, Carrier sig m) => Position -> Type -> m Kind
inferKind pos = cata (alg <=< sequence)
  where
    alg :: TypeF Kind -> m Kind
    alg = \case
      TRef tv              -> return (tvKind tv)
      TMeta tv             -> return (etvKind tv)
      TForall _ k          -> return k
      T _                  -> return Star
      TE _                 -> return EStar
      TExpr EStar          -> return Star
      TArrow Star Star     -> return Star
      TPair Star Star      -> return Star
      TRecord Row          -> return Star
      TVariant Row         -> return Star
      TPresent             -> return Presence
      TAbsent              -> return Presence
      TRowEmpty            -> return Row
      TRowExtend _
         Presence Star Row -> return Row
      other                -> throwError (TCError pos (IllKindedType other))

----------------------------------------------------------------------

type InferM = ErrorC TCError (StateC CheckState PureC)

runInfer :: InferM a -> Either TCError a
runInfer = runPureC . evalState defCheckState . runError

inferExprType
  :: forall m sig p.
     ( TypeChecking sig
     , Carrier sig m
     , TypePrim (Sum (Map Const p))
     ) => Expr p -> m (Type, Type)
inferExprType expr = do
  t <- infer expr
  ctx <- getCtx
  pure (applySolutions ctx t, Fix TRowEmpty)
