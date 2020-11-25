{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}

module Syntax.Desugar (desugar) where

import Prelude hiding (id)

import Control.Arrow (first)
import Control.Carrier.Reader
import Control.Monad.Free

import Data.Fix (Fix(..))
import Data.Functor.Foldable (cata, futu)
import qualified Data.Map as M
import Data.Proxy
import Data.Text (pack)

import Language.Sexp.Located (Position(..))

import Expr (Variable(..))
import qualified Expr as Raw
import qualified Prim.Base as Raw (BasePrim(..), BaseType(..))
import qualified Prim.Dyn as Raw (DynPrim(..))
import qualified Prim.Exception as Raw (ExceptionPrim(..))
import qualified Prim.IO as Raw (IOPrim(..))
import qualified Prim.Kappa as Raw (KappaPrim(..), EPrim(..), KappaType(..))
import qualified Prim.Link.Types as Raw (LinkPrim(..))
import qualified Prim.Record as Raw (RecordPrim(..))
import qualified Prim.Variant as Raw (VariantPrim(..))
import qualified Syntax.Position as Raw
import Syntax.Sugared
import Utils

dsPos :: Position -> Raw.Position
dsPos (Position fn l c) = Raw.Position (pack fn) l c l c

desugar :: forall t p.
  ( Raw.BasePrim      :<< p
  , Raw.DynPrim       :<< p
  , Raw.ExceptionPrim :<< p
  , Raw.IOPrim        :<< p
  , Raw.KappaPrim     :<< p
  , Raw.LinkPrim      :<< p
  , Raw.RecordPrim    :<< p
  , Raw.VariantPrim   :<< p
  , Raw.BaseType      :<< t
  , Raw.KappaType     :<< t
  ) => Sugared -> Raw.Expr t p
desugar = resolvePrimitives . futu coalg
  where
    dummyVar = Variable "_"

    mkLambda pos bindings e =
      foldr (\b' rest_ -> Free $ Raw.Lambda pos b' rest_) e bindings

    mkApp pos f args =
      foldl (\acc arg -> Free $ Raw.App pos acc arg) f args

    unFree :: forall f a. Free f a -> f (Free f a)
    unFree = \case
      Free x -> x
      Pure _ -> error "Desugaring coalgebra was not able to generate even a single layer of desugaring!"

    coalg :: Sugared -> Raw.ExprF t p (Free (Raw.ExprF t p) Sugared)
    coalg = \case
      Fix (Var pos var) ->
        Raw.Ref (dsPos pos) var

      Fix (Lambda pos b bs e) ->
        unFree $ mkLambda (dsPos pos) (b:bs) (Pure e)

      Fix (App pos f a as) ->
        unFree $ mkApp (dsPos pos) (Pure f) (map Pure (a:as))

      Fix (Let pos b bs e) ->
        let (name, expr) = desugarBinding b
        in Raw.Let (dsPos pos) name expr
             (foldr (\(x, a) rest_ -> Free $ Raw.Let (dsPos pos) x a rest_) (Pure e) (map desugarBinding bs))
        where
          desugarBinding :: LetBinding Sugared -> (Variable, Free (Raw.ExprF t p) Sugared)
          desugarBinding (LetBinding n expr) = (n, Pure expr)

      Fix (Literal pos lit) ->
        case lit of
          LitBool  x -> Raw.Prim (dsPos pos) (inject' (Raw.MkBool x))
          LitFloat x -> Raw.Prim (dsPos pos) (inject' (Raw.MkFloat x))
          LitStr   x -> Raw.Prim (dsPos pos) (inject' (Raw.MkText x))
          LitUnit    -> Raw.Prim (dsPos pos) (inject' Raw.MkUnit)

      Fix (If pos cond tr fls) ->
        unFree $
          mkApp (dsPos pos) (Free $ Raw.Prim (dsPos pos) (inject' Raw.If))
            [ Pure cond
            , mkLambda (dsPos pos) [dummyVar] (Pure tr)
            , mkLambda (dsPos pos) [dummyVar] (Pure fls)
            ]

      Fix (MkList pos xs) ->
        let lnil  = Free $ Raw.Prim (dsPos pos) (inject' Raw.ListNil)
            lcons x xs' = mkApp (dsPos pos) (Free $ Raw.Prim (dsPos pos) (inject' Raw.ListCons)) [Pure x, xs']
        in unFree $ foldr lcons lnil xs

      Fix (MkTuple pos a b cs) ->
        let primCons = Free (Raw.Prim (dsPos pos) (inject' Raw.MkPair))
            app f x = Free (Raw.App (dsPos pos) f x)
            (e : es) = reverse (a : b : cs)
        in unFree $
             foldr
               (\x rest_ -> (primCons `app` Pure x) `app` rest_)
               (Pure e)
               (reverse es)

      Fix (MkRec pos elems) ->
        let empty = Raw.Prim (dsPos pos) (inject' Raw.RecordNil)
            ext lbl p r = Raw.App (dsPos pos) (Free (Raw.App (dsPos pos) (Free (Raw.Prim (dsPos pos) (inject' (Raw.RecordExtend lbl)))) p)) r
        in unFree $
             foldr
               (\(lbl, e) rest_ -> Free $ ext lbl (Pure e) rest_)
               (Free empty)
               elems

      Fix (RecProj pos label record) ->
        Raw.App (dsPos pos)
          (Free (Raw.Prim (dsPos pos) (inject' (Raw.RecordSelect label))))
          (Pure record)

      Fix (RecDef pos label record def) ->
        Raw.App (dsPos pos)
          (Free (Raw.App (dsPos pos) (Free (Raw.Prim (dsPos pos) (inject' (Raw.RecordDefault label)))) (Pure def)))
          (Pure record)

      Fix (RecExt pos label record payload) ->
        Raw.App (dsPos pos)
          (Free (Raw.App (dsPos pos) (Free (Raw.Prim (dsPos pos) (inject' (Raw.RecordExtend label)))) (Pure payload)))
          (Pure record)

      Fix (MkVnt pos lbl) ->
        Raw.Prim (dsPos pos) (inject' (Raw.VariantInject lbl))

      Fix (Case pos scrutinee alts) ->
        let primDecomp lbl = Free (Raw.Prim (dsPos pos) (inject' (Raw.VariantDecomp lbl)))
            primAbsurd = Free (Raw.Prim (dsPos pos) (inject' Raw.VariantAbsurd))
            app f a = Free (Raw.App (dsPos pos) f a)
            lam v b = Free (Raw.Lambda (dsPos pos) v b)
            decompose lbl v handle = primDecomp lbl `app` lam v handle
        in unFree $
             flip app (Pure scrutinee) $
             foldr
               (\case
                   VariantMatchCase lbl v e -> app (decompose lbl v (Pure e))
                   VariantCatchAll v e -> \_ -> lam v (Pure e))
               primAbsurd
               alts

      Fix (Delay pos expr) ->
        Raw.App (dsPos pos)
          (Free (Raw.Prim (dsPos pos) (inject' Raw.Delay)))
          (Free (Raw.Lambda (dsPos pos) (Variable "_") (Pure expr)))

      Fix (Force pos expr) ->
        Raw.App (dsPos pos)
          (Pure expr)
          (Free (Raw.Prim (dsPos pos) (inject' Raw.MkUnit)))

      Fix (DoBlock pos stmts) ->
        let mkSeq p x a b = Free (Raw.App (dsPos p) (Free (Raw.Lambda (dsPos p) x b)) (Pure a)) in
        case stmts of
          [] -> error "Impossible empty do-block"
          (_:_) ->
            let bind bnd rest_ =
                  let (var, expr) = case bnd of
                        IgnoringBinding e -> (dummyVar, e)
                        OrdinarySeqBinding x e -> (x, e)
                  in mkSeq pos var expr rest_
            in unFree $
                foldr bind
                  (case last stmts of
                      IgnoringBinding e -> mkSeq pos dummyVar e (Free (Raw.Ref (dsPos pos) dummyVar))
                      OrdinarySeqBinding x e -> mkSeq pos x e (Free (Raw.Prim (dsPos pos) (inject' Raw.MkUnit))))
                  (init stmts)

      Fix (Loop pos xs body) ->
        let primLoop = Free (Raw.Prim (dsPos pos) (inject' (Raw.KLoop)))
            app f a  = Free (Raw.App (dsPos pos) f a)
            lam v b  = Free (Raw.Lambda (dsPos pos) v b)
        in unFree $
             foldr
               (\bnd rest_ -> primLoop `app` lam bnd rest_)
               (Pure body)
               (reverse xs)

      Fix (Catch pos cont handlers) ->
        let primDecomp lbl = Free (Raw.Prim (dsPos pos) (inject' (Raw.VariantDecomp lbl)))
            primCatch = Free (Raw.Prim (dsPos pos) (inject' Raw.CatchExc))
            primRaise = Free (Raw.Prim (dsPos pos) (inject' Raw.RaiseExc))
            app f a = Free (Raw.App (dsPos pos) f a)
            lam v b = Free (Raw.Lambda (dsPos pos) v b)
            decompose lbl v handle = primDecomp lbl `app` lam v handle
        in unFree $
             app (app primCatch (Pure cont)) $
             foldr
               (\case
                   VariantMatchCase lbl v e -> app (decompose lbl v (Pure e))
                   VariantCatchAll v e -> \_ -> lam v (Pure e))
               primRaise
               handlers

      Fix (Prev pos expr) ->
        let primLoop = Free (Raw.Prim (dsPos pos) (inject' (Raw.KLoop)))
            app f a  = Free (Raw.App (dsPos pos) f a)
            lam v b  = Free (Raw.Lambda (dsPos pos) v b)
            tuple :: Sugared
            tuple = Fix (MkTuple pos expr (Fix (Var pos (Variable "ξ"))) [])
        in unFree $ primLoop `app` lam (Variable "ξ") (Pure tuple)


primitives :: forall p proxy.
  ( Raw.BasePrim      :<< p
  , Raw.DynPrim       :<< p
  , Raw.ExceptionPrim :<< p
  , Raw.IOPrim        :<< p
  , Raw.KappaPrim     :<< p
  , Raw.LinkPrim      :<< p
  ) => proxy p -> M.Map Variable (Int, Sum' p)
primitives _ = M.fromList
  [ (Variable "+",           (0, inject' Raw.Add))
  , (Variable "readnum",     (0, inject' Raw.ReadDouble))
  , (Variable "shownum",     (0, inject' Raw.ShowDouble))

    -- Dyn
  , (Variable "new",         (0, inject' Raw.NewVar))
  , (Variable "new-global",  (0, inject' Raw.NewGlobalVar))
  , (Variable "ask",         (0, inject' Raw.AskVar))
  , (Variable "with",        (0, inject' Raw.SetVar))

    -- IO
  , (Variable "readln",      (0, inject' Raw.ReadLn))
  , (Variable "writeln",     (0, inject' Raw.WriteLn))

    -- Lists
  , (Variable "cons",        (0, inject' Raw.ListCons))

  , (Variable "fst",         (0, inject' Raw.PairFst))
  , (Variable "snd",         (0, inject' Raw.PairSnd))

    -- Link
  , (Variable "link",        (0, inject' Raw.Link))

    -- Exception
  , (Variable "raise",       (0, inject' Raw.RaiseExc))

    -- Kappa
  , (Variable "k/bool",      (0, inject' Raw.KConstBool))
  , (Variable "k/dbl",       (0, inject' Raw.KConstDbl))
  , (Variable "k/vec",       (0, inject' Raw.KConstVec))
  , (Variable "k/+",         (0, inject' (Raw.KPrim Raw.EAdd)))
  , (Variable "k/*",         (0, inject' (Raw.KPrim Raw.EMul)))
  , (Variable "k/-",         (0, inject' (Raw.KPrim Raw.ESub)))
  , (Variable "k/%",         (0, inject' (Raw.KPrim Raw.EDiv)))
  , (Variable "k/fold",      (0, inject' (Raw.KPrim Raw.EFold)))
  , (Variable "k/map",       (0, inject' (Raw.KPrim Raw.EMap)))
  , (Variable "k/if",        (0, inject' (Raw.KPrim Raw.EBranch)))
  , (Variable "k/loop",      (0, inject' Raw.KLoop))
  ]

resolvePrimitives ::
  forall t p.
  ( Raw.BasePrim      :<< p
  , Raw.DynPrim       :<< p
  , Raw.ExceptionPrim :<< p
  , Raw.IOPrim        :<< p
  , Raw.KappaPrim     :<< p
  , Raw.LinkPrim      :<< p
  , Raw.BaseType      :<< t
  , Raw.KappaType     :<< t
  ) => Raw.Expr t p -> Raw.Expr t p
resolvePrimitives expr = run . runReader (primitives (Proxy @p)) $ cata alg expr
  where
    alg :: forall m sig r.
           ( r ~ M.Map Variable (Int, Sum' p)
           , Has (Reader r) sig m
           ) => Raw.ExprF t p (m (Raw.Expr t p)) -> m (Raw.Expr t p)
    alg = \case
      Raw.Ref pos var -> do
        val <- asks @r (M.lookup var)
        case val of
          Just (m, c) | m == 0 -> return (Fix (Raw.Prim pos c))
          _ -> return (Fix (Raw.Ref pos var))

      Raw.Lambda pos var body -> do
        body' <- local @r (M.adjust (first succ) var) body
        return (Fix (Raw.Lambda pos var body'))

      Raw.App pos f a -> do
        f' <- f
        a' <- a
        return (Fix (Raw.App pos f' a'))

      Raw.Let pos var b a -> do
        b' <- b
        a' <- local @r (M.adjust (first succ) var) a
        return (Fix (Raw.Let pos var b' a'))

      Raw.Annot pos e t -> do
        e' <- e
        return (Fix (Raw.Annot pos e' t))

      Raw.Prim pos c ->
        return (Fix (Raw.Prim pos c))

