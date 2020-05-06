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

module TypeChecker (runInfer, check, inferExprType) where

import Control.Monad

import Control.Effect.Carrier
import Control.Effect.Error
import Control.Effect.Pure
import Control.Effect.Reader
import Control.Effect.State
import Control.Effect.Writer

import Data.Foldable (toList, fold)
import Data.Functor.Foldable (Fix (..), cata)
import Data.Maybe
import Data.Monoid (All(..), Any(..))
import Data.Proxy
import Data.Sequence (Seq(..))
import qualified Data.Sequence as Seq
import Data.Sum
import Data.Text.Prettyprint.Doc as PP

import qualified Debug.Trace

import Syntax.Position
import Errors
import Expr
import Types
import Utils
import Pretty

trace :: String -> a -> a
trace = if False then Debug.Trace.trace else flip const

isMono :: Type t -> Bool
isMono = getAll . cata alg
  where
    alg = \case
      TForall _ _ -> All False
      TExists _ _ -> All False
      other -> fold other

data CtxMember t
  = CtxVar    TVar
  | CtxAssump Variable (Type t)
  | CtxMeta   MetaVar
  | CtxSolved MetaVar (Type t)
  | CtxMarker MetaVar

instance Eq (CtxMember t) where
  CtxVar x == CtxVar y = x == y
  CtxAssump x _ == CtxAssump y _ = x == y
  CtxMeta x == CtxMeta y = x == y
  CtxSolved x _ == CtxSolved y _ = x == y
  CtxMarker x == CtxMarker y = x == y
  _ == _ = False

newtype Ctx t = Ctx (Seq (CtxMember t))
  deriving (Semigroup, Monoid)

ppCtx :: forall t ann. Apply' Pretty1 t => Ctx t -> Doc ann
ppCtx (Ctx elems) = indent 2 . vsep . map ppMember . toList $ elems
  where
    ppMember :: CtxMember t -> Doc ann
    ppMember = \case
      CtxVar tv       -> "skolem" <+> ppTyVar tv
      CtxAssump v ty  -> "assump" <+> ppVariable v <+> ":" <+> ppType ty
      CtxMeta ev      -> "unsolv" <+> ppMetaVar ev
      CtxSolved ev ty -> "solved" <+> ppMetaVar ev <+> "=" <+> ppType ty
      CtxMarker ev    -> "marker" <+> "▸" <> ppMetaVar ev

(▸) :: Ctx t -> CtxMember t -> Ctx t
(Ctx ctx) ▸ mem = Ctx (ctx :|> mem)

ctxHole :: CtxMember t -> Ctx t -> Maybe (Ctx t, Ctx t)
ctxHole mem (Ctx ctx) =
  let (front, rear) = Seq.breakr (== mem) ctx
  in case rear of
       Empty -> Nothing
       rear' :|> _ -> Just (Ctx rear', Ctx front)

ctxHoles :: CtxMember t -> CtxMember t -> Ctx t -> Maybe (Ctx t, Ctx t, Ctx t)
ctxHoles x y ctx = do
  (a, rest) <- ctxHole x ctx
  (b, c)    <- ctxHole y rest
  return (a, b, c)

ctxAssump :: Ctx t -> Variable -> Maybe (Type t)
ctxAssump (Ctx ctx) x = go ctx
  where
    go = \case
      Empty -> Nothing
      _    :|> CtxAssump y t | x == y -> Just t
      rest :|> _ -> go rest

ctxSolution :: Ctx t -> MetaVar -> Maybe (Type t)
ctxSolution (Ctx ctx) x = go ctx
  where
    go = \case
      Empty -> Nothing
      _    :|> CtxSolved y t | x == y -> Just t
      _    :|> CtxMeta   y   | x == y -> Nothing
      rest :|> _ -> go rest

ctxHasSkolem :: Ctx t -> TVar -> Bool
ctxHasSkolem (Ctx ctx) v =
  CtxVar v `elem` ctx

ctxHasMeta :: Ctx t -> MetaVar -> Bool
ctxHasMeta (Ctx ctx) x = go ctx
  where
    go = \case
      Empty -> False
      _    :|> CtxSolved y _ | x == y -> True
      _    :|> CtxMeta   y   | x == y -> True
      rest :|> _ -> go rest

ctxDrop :: CtxMember t -> Ctx t -> Ctx t
ctxDrop m (Ctx ctx) =
  Ctx $ Seq.dropWhileR (== m) $ Seq.dropWhileR (/= m) ctx

ctxUnsolved :: Ctx t -> ([MetaVar], Ctx t)
ctxUnsolved (Ctx ctx) =
  ( flip mapMaybe (toList ctx) $ \case
      CtxMeta m@MetaVar{} -> Just m
      _ -> Nothing
  , Ctx $ flip fmap ctx $ \case
      CtxMeta v@(MetaVar n k) -> CtxSolved v (Fix (TRef (TVar n k)))
      other -> other
  )

----------------------------------------------------------------------

(⊢) :: forall t. Ctx t -> Type t -> Either (Reason t) ()
(⊢) ctx0 ty = run $ runReader ctx0 $ runError (cata alg ty)
  where
    alg :: (Member (Error (Reason t)) sig, Member (Reader (Ctx t)) sig, Carrier sig m) =>
           TypeF t (m ()) -> m ()
    alg t = do
      ctx <- ask @(Ctx t)
      case t of
        TRef v ->
          unless (ctxHasSkolem ctx v) $
            throwError @(Reason t) $ TypeVariableNotFound v
        TMeta v ->
          unless (ctxHasMeta ctx v) $
            throwError @(Reason t) $ OtherError $ "unscoped meta variable ‘" ++ show v ++ "’"
        TForall v b ->
          local @(Ctx t) (▸ CtxVar v) b
        TExists v b ->
          local @(Ctx t) (▸ CtxVar v) b
        other -> sequence_ other

freeMetaIn :: forall t. MetaVar -> Type t -> Bool
freeMetaIn x = getAny . cata alg
  where
    alg :: TypeF t Any -> Any
    alg = \case
      TMeta v | x == v -> Any True
      other -> fold other

applySolutions :: forall t. Ctx t -> Type t -> Type t
applySolutions ctx = cata alg
  where
    alg :: TypeF t (Type t) -> Type t
    alg = \case
      TMeta v -> maybe (Fix (TMeta v)) (applySolutions ctx) (ctxSolution ctx v)
      other   -> Fix other

subst :: forall t. (TVar, Type t) -> Type t -> Type t
subst (v, s) = cata alg
  where
    alg :: TypeF t (Type t) -> Type t
    alg = \case
      TRef v' | v == v' -> s
      other -> Fix other

----------------------------------------------------------------------

type TypeChecking t sig =
  ( Member (State (CheckState t)) sig
  , Member (Error (TCError t)) sig
  , Member (Reader Position) sig
  , Effect sig
  )

data CheckState t = CheckState
  { checkCtx :: Ctx t
  , checkNextEVar :: Int
  }

defCheckState :: CheckState t
defCheckState = CheckState mempty 1

getCtx :: forall t sig m. (TypeChecking t sig, Carrier sig m) => m (Ctx t)
getCtx = gets @(CheckState t) checkCtx

putCtx :: forall t sig m. (TypeChecking t sig, Carrier sig m) => Ctx t -> m ()
putCtx ctx = get @(CheckState t) >>= \s -> put @(CheckState t) s { checkCtx = ctx }

modifyCtx :: (TypeChecking t sig, Carrier sig m) => (Ctx t -> Ctx t) -> m ()
modifyCtx f = putCtx . f =<< getCtx

freshMeta :: forall t sig m proxy. (TypeChecking t sig, Carrier sig m) => proxy t -> Kind -> m MetaVar
freshMeta _ k = do
  n <- gets @(CheckState t) checkNextEVar
  modify @(CheckState t) (\s -> s { checkNextEVar = checkNextEVar s + 1 })
  pure $ MetaVar n k

(≤) :: forall t sig m. (TypeChecking t sig, Carrier sig m, TypeConstructor t) => Type t -> Type t -> m ()
(≤) (Fix typeA) (Fix typeB) =
  getCtx @t >>= \ctx ->
    trace (render $ vsep [ "Checking:" <+> ppType (Fix typeA) <+> "≤" <+> ppType (Fix typeB), ppCtx ctx ]) $
      runReader id (typeA ≤⋆ typeB)
  where
    (≤⋆) :: (TypeChecking t sig, Carrier sig m) => TypeF t (Type t) -> TypeF t (Type t) -> ReaderC (m () -> m ()) m ()
    a ≤⋆ TForall v (Fix b) = do
      modifyCtx @t (▸ CtxVar v)
      a ≤⋆ b
      modifyCtx @t (ctxDrop (CtxVar v))

    TExists v (Fix a) ≤⋆ b = do
      modifyCtx @t (▸ CtxVar v)
      a ≤⋆ b
      modifyCtx @t (ctxDrop (CtxVar v))

    TForall v a ≤⋆ b = do
      ma <- freshMeta (Proxy @t) (tvKind v)
      let Fix a' = subst (v, Fix (TMeta ma)) a
      local @(m () -> m ())
        (\wrap act ->
           wrap $
             modifyCtx @t (\c -> c ▸ CtxMarker ma ▸ CtxMeta ma) >>
             act >>
             modifyCtx @t (ctxDrop (CtxMarker ma)))
        (a' ≤⋆ b)

    a ≤⋆ TExists v b = do
      mb <- freshMeta (Proxy @t) (tvKind v)
      let Fix b' = subst (v, Fix (TMeta mb)) b
      local @(m () -> m ())
        (\wrap act ->
           wrap $
             modifyCtx @t (\c -> c ▸ CtxMarker mb ▸ CtxMeta mb) >>
             act >>
             modifyCtx @t (ctxDrop (CtxMarker mb)))
        (a ≤⋆ b')

    monoA ≤⋆ monoB =
      ask @(m () -> m ()) >>= \wrapper ->
        ReaderC (\_ -> wrapper (monoA ≤· monoB))

    (≤·) :: (TypeChecking t sig, Carrier sig m) => TypeF t (Type t) -> TypeF t (Type t) -> m ()
    TRef a   ≤· TRef b  | a == b = return ()
    TMeta a  ≤· TMeta b | a == b = return ()
    TCtor a  ≤· TCtor b | a == b = return ()

    TApp f a ≤· TApp g b = do
      case filter (not . isMono) [f, g, a, b] of
        (t : _) -> ask @Position >>= \pos -> throwError $ TCError pos $ ImpredicativePolymoprhism t
        []      -> pure ()
      f ≤ g
      getCtx >>= \ctx -> applySolutions ctx a ≤ applySolutions ctx b

    TArrow a b ≤· TArrow a' b' = do
      a' ≤ a -- contravariant
      getCtx >>= \ctx -> applySolutions ctx b ≤ applySolutions ctx b'

    TMeta ma ≤· a | not (ma `freeMetaIn` Fix a) = instantiate Rigid ma (Fix a)
    a ≤· TMeta ma | not (ma `freeMetaIn` Fix a) = instantiate Flex  ma (Fix a)

    TUnit ≤· TUnit = pure ()
    TVoid ≤· TVoid = pure ()

    TSNil ≤· TSNil = pure ()
    TSCons h t ≤· TSCons h' t' = do
      h ≤ h'
      getCtx >>= \ctx -> applySolutions ctx t ≤ applySolutions ctx t'
    TEArrow a b ≤· TEArrow a' b' = do
      a' ≤ a -- contravariant
      getCtx >>= \ctx -> applySolutions ctx b ≤ applySolutions ctx b'

    TRecord a ≤· TRecord a' = a ≤ a'
    TVariant a ≤· TVariant a' = a ≤ a'

    TPresent ≤· TPresent = pure ()
    TAbsent ≤· TAbsent = pure ()

    TRowEmpty ≤· TRowEmpty = pure ()
    TRowExtend lbl pty fty tail_ ≤· TRowExtend lbl' pty' fty' tail' = do
      pos <- ask @Position
      (pty'', fty'', tail'') <- rewriteRow pos lbl lbl' pty' fty' tail'
      getCtx >>= \ctx -> applySolutions ctx pty   ≤ applySolutions ctx pty''
      getCtx >>= \ctx -> applySolutions ctx fty   ≤ applySolutions ctx fty''
      getCtx >>= \ctx -> applySolutions ctx tail_ ≤ applySolutions ctx tail''

    TRowEmpty ≤· TRowExtend lbl p f rest =
      (Fix (TRowExtend lbl (Fix TAbsent) f (Fix TRowEmpty))) ≤ (Fix (TRowExtend lbl p f rest))

    TRowExtend lbl p f rest ≤· TRowEmpty =
      (Fix (TRowExtend lbl p f rest)) ≤ (Fix (TRowExtend lbl (Fix TAbsent) f (Fix TRowEmpty)))

    a ≤· b = ask @Position >>= \pos -> -- Debug.Trace.trace (show a ++ "\n" ++ show b) $
      throwError $ TCError pos $ CannotUnify (Fix a) (Fix b)

rewriteRow
  :: forall t sig m. (TypeChecking t sig, Carrier sig m, TypeConstructor t) =>
     Position -> Label -> Label -> Type t -> Type t -> Type t -> m (Type t, Type t, Type t)
rewriteRow pos newLbl lbl pty fty tail_ =
  if newLbl == lbl
  then return (pty, fty, tail_)
  else
    case tail_ of
      Fix (TMeta alpha) -> do
        beta  <- freshMeta (Proxy @t) Row
        gamma <- freshMeta (Proxy @t) Star
        theta <- freshMeta (Proxy @t) Presence
        ctx1 <- getCtx @t
        case ctxHole (CtxMeta alpha) ctx1 of
          Just (l, r) -> do
            putCtx @t $ l
              ▸ CtxMeta beta
              ▸ CtxMeta gamma
              ▸ CtxMeta theta
              ▸ CtxSolved alpha (Fix (TRowExtend newLbl (Fix (TMeta theta)) (Fix (TMeta gamma)) (Fix (TMeta beta))))
              <> r
            getCtx @t >>= \ctx2 -> pure (Fix (TMeta theta), Fix (TMeta gamma), Fix (TRowExtend lbl (applySolutions ctx2 pty) (applySolutions ctx2 fty) (Fix (TMeta beta))))
          Nothing -> error "cannot instantiate var"
      Fix (TRowExtend lbl' pty' fty' tail') -> do
        (pty'', fty'', tail'') <- rewriteRow pos newLbl lbl' pty' fty' tail'
        getCtx >>= \ctx -> pure (pty'', fty'', Fix (TRowExtend lbl (applySolutions ctx pty) (applySolutions ctx fty) tail''))
      Fix TRowEmpty -> do
        gamma <- freshMeta (Proxy @t) Star
        pure (Fix TAbsent, Fix (TMeta gamma), Fix (TRowExtend lbl pty fty (Fix TRowEmpty)))
      _other ->
        error $ "Unexpected type: " ++ show tail_

data Direction = Flex | Rigid deriving (Eq, Ord, Show)

opposite :: Direction -> Direction
opposite = \case
  Flex -> Rigid
  Rigid -> Flex

instantiate :: forall t sig m. (TypeChecking t sig, Carrier sig m, TypeConstructor t) => Direction -> MetaVar -> Type t -> m ()
instantiate dir0 ma0 t0 = inst dir0 ma0 t0
  where
    inst :: (TypeChecking t sig, Carrier sig m) => Direction -> MetaVar -> Type t -> m ()
    inst dir ma t = getCtx >>= go
      where
        -- Inst*Solve
        go ctx | True <- isMono t, Just (l, r) <- ctxHole (CtxMeta ma) ctx, Right{} <- l ⊢ t =
          putCtx @t $ l ▸ CtxSolved ma t <> r

        -- Inst*Skolem
        go ctx | Just (l, _) <- ctxHole (CtxMeta ma) ctx, Fix (TRef tv) <- t, Left{} <- l ⊢ t = do
          ask @Position >>= \pos ->
            throwError $ TCError pos $ case dir0 of
              Rigid -> CannotUnifyWithSkolem (Fix (TMeta ma0)) t0 tv
              Flex  -> CannotUnifyWithSkolem t0 (Fix (TMeta ma0)) tv

        -- Inst*Reach
        go ctx | Fix (TMeta ma') <- t, Just (l, m, r) <- ctxHoles (CtxMeta ma) (CtxMeta ma') ctx =
          putCtx @t $ l ▸ CtxMeta ma <> m ▸ CtxSolved ma' (Fix (TMeta ma)) <> r

        -- Inst*Arr
        go ctx | Just (l, r) <- ctxHole (CtxMeta ma) ctx, Fix (TArrow a b) <- t = do
          ma1 <- freshMeta (Proxy @t) Star
          ma2 <- freshMeta (Proxy @t) Star
          putCtx @t $ l ▸ CtxMeta ma2 ▸ CtxMeta ma1 ▸ CtxSolved ma (Fix (TArrow (Fix (TMeta ma1)) (Fix (TMeta ma2)))) <> r
          inst (opposite dir) ma1 a
          getCtx @t >>= \ctx' -> inst dir ma2 (applySolutions ctx' b)

        -- Inst*Kappa
        go ctx | Just (l, r) <- ctxHole (CtxMeta ma) ctx, Fix (TEArrow a b) <- t = do
          ma1 <- freshMeta (Proxy @t) EStack
          ma2 <- freshMeta (Proxy @t) EStack
          putCtx @t $ l ▸ CtxMeta ma2 ▸ CtxMeta ma1 ▸ CtxSolved ma (Fix (TEArrow (Fix (TMeta ma1)) (Fix (TMeta ma2)))) <> r
          inst (opposite dir) ma1 a
          getCtx @t >>= \ctx' -> inst dir ma2 (applySolutions ctx' b)

        -- InstLAllR
        go ctx | Fix (TForall b s) <- t, Rigid <- dir = do
          putCtx @t $ ctx ▸ CtxVar b
          inst dir ma s
          modifyCtx @t (ctxDrop (CtxVar b))

        -- InstRAllL
        go ctx | Fix (TForall b s) <- t, Flex <- dir = do
          ma' <- freshMeta (Proxy @t) (tvKind b)
          putCtx @t $ ctx ▸ CtxMarker ma' ▸ CtxMeta ma'
          inst dir ma (subst (b, Fix (TMeta ma')) s)
          modifyCtx @t (ctxDrop (CtxMarker ma'))

        -- InstLExistsR
        go ctx | Fix (TExists b s) <- t, Rigid <- dir = do
          ma' <- freshMeta (Proxy @t) (tvKind b)
          putCtx @t $ ctx ▸ CtxMarker ma' ▸ CtxMeta ma'
          inst dir ma (subst (b, Fix (TMeta ma')) s)
          modifyCtx @t (ctxDrop (CtxMarker ma'))

        -- InstRExistsL
        go ctx | Fix (TExists b s) <- t, Flex <- dir = do
          putCtx @t $ ctx ▸ CtxVar b
          inst dir ma s
          modifyCtx @t (ctxDrop (CtxVar b))

        -- InstOther
        go ctx | Just (l, r) <- ctxHole (CtxMeta ma) ctx, Fix t' <- t = do
          (tasks :: [(MetaVar, Type t)], t'') <- runWriter $ forM t' $ \a -> do
            k <- inferKind dummyPos a
            ma' <- freshMeta (Proxy @t) k
            tell [(ma', a)]
            return (Fix (TMeta ma'))
          putCtx $ foldl (▸) l (map (CtxMeta . fst) tasks) ▸ CtxSolved ma (Fix t'') <> r
          forM_ tasks $ \(mv, a) ->
            getCtx >>= \ctx' -> inst dir mv (applySolutions ctx' a)

        go _ = error $ "internal error: failed to instantiate " ++ show ma ++ " to " ++ show t

----------------------------------------------------------------------

check
  :: forall t p sig m.
     ( TypeChecking t sig
     , Carrier sig m
     , TypePrim t (Sum (Map Const p))
     , TypeConstructor t
     )
  => Expr t p
  -> Type t
  -> m ()

check e (Fix (TForall v a)) = do
  modifyCtx @t (▸ CtxVar v)
  check e a
  modifyCtx @t (ctxDrop (CtxVar v))

check e (Fix (TExists v a)) = do
  ma' <- freshMeta (Proxy @t) (tvKind v)
  modifyCtx @t $ \ctx -> ctx ▸ CtxMarker ma' ▸ CtxMeta ma'
  check e (subst (v, Fix (TMeta ma')) a)
  modifyCtx @t (ctxDrop (CtxMarker ma'))

check (Fix (Lambda _ x e)) (Fix (TArrow a b)) = do
  modifyCtx @t (▸ CtxAssump x a)
  check e b
  modifyCtx @t (ctxDrop (CtxAssump x a))

check e b = do
  a <- infer e
  void $ inferKind (exprPosition e) a
  local @Position (const (exprPosition e)) $
    getCtx @t >>= \ctx -> applySolutions ctx a ≤ applySolutions ctx b

----------------------------------------------------------------------

infer
  :: forall t p sig m.
     ( TypeChecking t sig
     , Carrier sig m
     , TypePrim t (Sum (Map Const p))
     , TypeConstructor t
     )
  => Expr t p
  -> m (Type t)

infer (Fix (Ref pos x)) = do
  ctx <- getCtx @t
  case ctxAssump ctx x of
    Nothing -> throwError @(TCError t) $ TCError pos $ VariableNotFound x
    Just t  -> return t

infer (Fix (Annot pos e t)) = do
  ctx <- getCtx @t
  case ctx ⊢ t of
    Left reason -> throwError $ TCError pos $ reason
    Right ()    -> check e t >> return t

infer (Fix (Lambda _ x e)) = do
  ma  <- freshMeta (Proxy @t) Star
  ma' <- freshMeta (Proxy @t) Star
  modifyCtx @t $ \c -> c ▸ CtxMarker ma ▸ CtxMeta ma ▸ CtxMeta ma' ▸ CtxAssump x (Fix (TMeta ma))
  check e (Fix (TMeta ma'))
  ctx <- getCtx @t
  case ctxHole (CtxMarker ma) ctx of
    Just (l, r) -> do
      let tau = applySolutions r (Fix (TArrow (Fix (TMeta ma)) (Fix (TMeta ma'))))
      putCtx @t l
      let (vars, r') = ctxUnsolved r
      pure $ foldr
        (\(MetaVar y k) -> Fix . TForall (TVar y k))
        (applySolutions r' tau)
        (filter (`freeMetaIn` tau) vars)
    Nothing -> error "internal error: could not find marker"

infer (Fix (App _ e1 e2)) = do
  a <- infer e1
  ctx <- getCtx @t
  inferApp (applySolutions ctx a) e2

infer (Fix (Let _ x e1 e2)) = do
  ma <- freshMeta (Proxy @t) Star
  mb <- freshMeta (Proxy @t) Star
  modifyCtx @t $ \c -> c ▸ CtxMarker ma ▸ CtxMeta ma ▸ CtxMeta mb ▸ CtxAssump x (Fix (TMeta ma))
  check e1 (Fix (TMeta ma))
  check e2 (Fix (TMeta mb))
  return (Fix (TMeta mb))

infer (Fix (Prim _ c)) =
  pure (toType (typePrim c))

----------------------------------------------------------------------

inferApp
  :: forall t p sig m.
     ( TypeChecking t sig
     , Carrier sig m
     , TypePrim t (Sum (Map Const p))
     , TypeConstructor t
     )
  => Type t
  -> Expr t p
  -> m (Type t)

inferApp (Fix (TForall v a)) e = do
  ma <- freshMeta (Proxy @t) (tvKind v)
  modifyCtx @t (▸ CtxMeta ma)
  inferApp (subst (v, Fix (TMeta ma)) a) e

inferApp (Fix (TExists v a)) e = do
  modifyCtx @t (▸ CtxVar v)
  t <- inferApp a e
  modifyCtx @t (ctxDrop (CtxVar v))
  return t

inferApp (Fix (TMeta ma)) e = do
  ma1 <- freshMeta (Proxy @t) Star
  ma2 <- freshMeta (Proxy @t) Star
  ctx <- getCtx @t
  let Just (l, r) = ctxHole (CtxMeta ma) ctx
  putCtx $ l ▸ CtxMeta ma2 ▸ CtxMeta ma1 ▸ CtxSolved ma (Fix (TArrow (Fix (TMeta ma1)) (Fix (TMeta ma2)))) <> r
  check e (Fix (TMeta ma1))
  return (Fix (TMeta ma2))

inferApp (Fix (TArrow a c)) e = do
  check e a
  return c

inferApp t e =
  throwError @(TCError t) $ TCError (exprPosition e) $
    OtherError $ "cannot apply to expression of type " ++ show (ppType t)

----------------------------------------------------------------------

inferKind :: forall t sig m. (TypeChecking t sig, Carrier sig m, TypeConstructor t) => Position -> Type t -> m Kind
inferKind pos = cata (alg <=< sequence)
  where
    alg :: TypeF t Kind -> m Kind
    alg = \case
      -- Base
      TRef tv              -> return (tvKind tv)
      TMeta tv             -> return (etvKind tv)
      TForall _ k          -> return k
      TExists _ k          -> return k
      TApp (Arr a b) c
        | a == c           -> return b

      -- Primitive types
      TArrow Star Star     -> return Star
      TUnit                -> return Star
      TVoid                -> return Star

      -- External type constructors
      TCtor c              -> pure (kindOfCtor c)

      -- Embedded language
      TSNil                 -> return EStack
      TSCons EStar EStack   -> return EStack
      TEArrow EStack EStack -> return Star

      -- Row types
      TRecord Row          -> return Star
      TVariant Row         -> return Star
      TPresent             -> return Presence
      TAbsent              -> return Presence
      TRowEmpty            -> return Row
      TRowExtend _
        Presence Star Row  -> return Row

      other                -> throwError (TCError pos (IllKindedType other))

----------------------------------------------------------------------

type InferM t = ErrorC (TCError t) (StateC (CheckState t) (ReaderC Position PureC))

runInfer :: forall t a. InferM t a -> Either (TCError t) a
runInfer = runPureC . runReader dummyPos . evalState defCheckState . runError

inferExprType
  :: forall t m sig p.
     ( TypeChecking t sig
     , Carrier sig m
     , TypePrim t (Sum (Map Const p))
     , TypeConstructor t
     ) => Expr t p -> m (Type t)
inferExprType expr = do
  t <- infer expr
  void $ inferKind (exprPosition expr) t
  ctx <- getCtx
  pure (applySolutions ctx t)
