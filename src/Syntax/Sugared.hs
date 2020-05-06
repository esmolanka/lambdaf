{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}

{-# OPTIONS_GHC -O0 #-}

module Syntax.Sugared where

import Prelude hiding (id)

import Control.Arrow (first)
import Control.Category (id, (>>>))
import Control.Monad.Free
import Control.Effect.Reader

import Data.Coerce
import Data.Char (isUpper)
import Data.Functor.Foldable (Fix(..), cata, futu)
import qualified Data.Map as M
import Data.Proxy
import Data.Text (Text, pack, uncons)
import GHC.Generics

import Language.Sexp.Located (Position(..))
import Language.SexpGrammar
import Language.SexpGrammar.Generic

import Expr (Variable(..))
import qualified Expr as Raw
import qualified Prim.Base as Raw (BasePrim(..), BaseType(..))
import qualified Prim.Exception as Raw (ExceptionPrim(..))
import qualified Prim.IO as Raw (IOPrim(..))
import qualified Prim.Link.Types as Raw (LinkPrim(..))
import qualified Prim.Record as Raw (RecordPrim(..))
import qualified Prim.Variant as Raw (VariantPrim(..))
import qualified Prim.Kappa as Raw (KappaPrim(..), EPrim(..), KappaType(..))
import qualified Syntax.Position as Raw
import Types
import Utils

data Literal
  = LitBool  Bool
  | LitFloat Double
  | LitStr   Text
  | LitUnit
    deriving (Generic)

data LetBinding e = LetBinding Variable e
    deriving (Generic)

data SeqBinding e
  = IgnoringBinding e
  | OrdinarySeqBinding Variable e
    deriving (Generic)

data VariantMatchLeg e
  = VariantMatchCase Label Variable e
  | VariantCatchAll Variable e
    deriving (Generic)

type Sugared = Fix SugaredF
data SugaredF e
  = Var     Position Variable
  | Lambda  Position Variable [Variable] e
  | App     Position e e [e]
  | Let     Position (LetBinding e) [LetBinding e] e
  | Literal Position Literal
  | If      Position e e e
  | MkList  Position [e]
  | MkTuple Position e e [e]
  | MkRec   Position [(Label, e)]
  | RecProj Position Label e
  | RecDef  Position Label e e
  | RecExt  Position Label e e
  | MkVnt   Position Label
  | Case    Position e [VariantMatchLeg e]
  | Delay   Position e
  | Force   Position e
  | DoBlock Position [SeqBinding e]
  | Loop    Position [Variable] e
  | Kappa   Position [Variable] e
  | Catch   Position e [VariantMatchLeg e]
    deriving (Generic)

dsPos :: Position -> Raw.Position
dsPos (Position fn l c) = Raw.Position (pack fn) l c l c

desugar :: forall t p.
  ( Raw.BasePrim :<< p
  , Raw.RecordPrim :<< p
  , Raw.VariantPrim :<< p
  , Raw.IOPrim :<< p
  , Raw.KappaPrim :<< p
  , Raw.LinkPrim :<< p
  , Raw.ExceptionPrim :<< p
  , Raw.BaseType :<< t
  , Raw.KappaType :<< t
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
        let primCons = Free (Raw.Prim (dsPos pos) (inject' Raw.KCons))
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
                      OrdinarySeqBinding x e -> mkSeq pos x e (Free (Raw.Ref (dsPos pos) x)))
                  (init stmts)

      Fix (Loop pos xs body) ->
        let primLoop = Free (Raw.Prim (dsPos pos) (inject' (Raw.KPrim Raw.ELoop)))
            primKappa = Free (Raw.Prim (dsPos pos) (inject' Raw.KAbs))
            app f a  = Free (Raw.App (dsPos pos) f a)
            lam v b  = Free (Raw.Lambda (dsPos pos) v b)
        in unFree $
             foldr
               (\bnd rest_ -> primLoop `app` (primKappa `app` lam bnd rest_))
               (Pure body)
               (reverse xs)

      Fix (Kappa pos xs body) ->
        let app f a = Free (Raw.App (dsPos pos) f a)
            lam v b = Free (Raw.Lambda (dsPos pos) v b)
            primKappa = Free (Raw.Prim (dsPos pos) (inject' Raw.KAbs))
            wrap_ x rest_ = primKappa `app` lam x rest_
        in unFree $
             foldr wrap_ (Pure body) xs

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

primitives :: forall p proxy.
  ( Raw.BasePrim :<< p
  , Raw.IOPrim :<< p
  , Raw.KappaPrim :<< p
  , Raw.LinkPrim :<< p
  , Raw.ExceptionPrim :<< p
  ) => proxy p -> M.Map Variable (Int, Sum' p)
primitives _ = M.fromList
  [ (Variable "+",           (0, inject' Raw.Add))
  , (Variable "readnum",     (0, inject' Raw.ReadDouble))
  , (Variable "shownum",     (0, inject' Raw.ShowDouble))

    -- IO
  , (Variable "readln",      (0, inject' Raw.ReadLn))
  , (Variable "writeln",     (0, inject' Raw.WriteLn))

    -- Lists
  , (Variable "cons",        (0, inject' Raw.ListCons))

    -- Link
  , (Variable "link",        (0, inject' Raw.Link))

    -- Exception
  , (Variable "raise",       (0, inject' Raw.RaiseExc))

    -- Kappa
  , (Variable "^bool",       (0, inject' Raw.KConstBool))
  , (Variable "^dbl",        (0, inject' Raw.KConstDbl))
  , (Variable "^vec",        (0, inject' Raw.KConstVec))
  , (Variable "^add",        (0, inject' (Raw.KPrim Raw.EAdd)))
  , (Variable "^mul",        (0, inject' (Raw.KPrim Raw.EMul)))
  , (Variable "^sub",        (0, inject' (Raw.KPrim Raw.ESub)))
  , (Variable "^div",        (0, inject' (Raw.KPrim Raw.EDiv)))
  , (Variable "^fold",       (0, inject' (Raw.KPrim Raw.EFold)))
  , (Variable "^branch",     (0, inject' (Raw.KPrim Raw.EBranch)))
  , (Variable "^head",       (0, inject' Raw.KFirst))
  , (Variable "^tail",       (0, inject' Raw.KRest))
  ]

resolvePrimitives ::
  forall t p.
  ( Raw.BasePrim :<< p
  , Raw.IOPrim :<< p
  , Raw.KappaPrim :<< p
  , Raw.LinkPrim :<< p
  , Raw.ExceptionPrim :<< p
  , Raw.BaseType :<< t
  , Raw.KappaType :<< t
  ) => Raw.Expr t p -> Raw.Expr t p
resolvePrimitives expr = run . runReader (primitives (Proxy @p)) $ (cata alg expr)
  where
    alg :: forall m sig r.
           ( r ~ M.Map Variable (Int, Sum' p)
           , Member (Reader r) sig
           , Carrier sig m
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


----------------------------------------------------------------------
-- Grammars

varGrammar :: Grammar Position (Sexp :- t) (Variable :- t)
varGrammar =
  symbol >>>
  partialOsi parseVar coerce
  where
    parseVar :: Text -> Either Mismatch Variable
    parseVar t
      | t `elem` ["lambda","let","if","case","catch","do","loop","kappa","=","<-","**","tt","ff"] = Left (unexpected t)
      | Just (h, _) <- uncons t, h == ':' || isUpper h = Left (unexpected t)
      | otherwise = Right (Variable t)


ctorLabelGrammar :: Grammar Position (Sexp :- t) (Label :- t)
ctorLabelGrammar =
  symbol >>>
  partialOsi parseCtor coerce
  where
    parseCtor :: Text -> Either Mismatch Label
    parseCtor t
      | Just (h, _) <- uncons t, isUpper h = Right (Label t)
      | otherwise = Left (unexpected t)


labelGrammar :: Grammar Position (Sexp :- t) (Label :- t)
labelGrammar = keyword >>> iso coerce coerce


bindingGrammar :: Grammar Position (Sexp :- t) (LetBinding Sugared :- t)
bindingGrammar = with $ \bnd ->
  bracketList (
    el varGrammar >>>
    el sugaredGrammar) >>>
  bnd


seqStmtGrammar :: Grammar Position (Sexp :- t) (SeqBinding Sugared :- t)
seqStmtGrammar = match
  $ With (\ign ->
      sugaredGrammar >>>
      ign)
  $ With (\bnd ->
      braceList (
        el varGrammar >>>
        el (sym "<-") >>>
        el sugaredGrammar) >>>
      bnd)
  $ End


variantMatchLegGrammar :: Grammar Position (Sexp :- t) (VariantMatchLeg Sugared :- t)
variantMatchLegGrammar = match
  $ With (\pat ->
      bracketList (
        el (list (
              el ctorLabelGrammar >>>
              el varGrammar)) >>>
        el sugaredGrammar) >>>
      pat)
  $ With (\catchall ->
      bracketList (
        el varGrammar >>>
        el sugaredGrammar) >>>
      catchall)
  $ End


boolGrammar :: Grammar Position (Sexp :- t) (Bool :- t)
boolGrammar = symbol >>> partialOsi
  (\case
      "tt" -> Right True
      "ff" -> Right False
      other -> Left $ expected "bool" <> unexpected ("symbol " <> other))
  (\case
      True -> "tt"
      False -> "ff")


litGrammar :: Grammar Position (Sexp :- t) (Literal :- t)
litGrammar = match
  $ With (\litb -> boolGrammar >>> litb)
  $ With (\litf -> double      >>> litf)
  $ With (\lits -> string      >>> lits)
  $ With (\litu -> list id     >>> litu)
  $ End


sugaredGrammar :: Grammar Position (Sexp :- t) (Sugared :- t)
sugaredGrammar = fixG $ match
  $ With (\var ->
             annotated "variable" $
             position >>>
             swap >>>
             varGrammar >>> var)

  $ With (\lam ->
             annotated "lambda" $
             position >>>
             swap >>>
             list (
               el (sym "lambda") >>>
               el (list (
                     el varGrammar >>>
                     rest varGrammar)) >>>
               el sugaredGrammar) >>>
             lam)

  $ With (\app ->
            position >>>
            swap >>>
            list (
             el sugaredGrammar >>>
             el sugaredGrammar >>>
             rest sugaredGrammar) >>> app)

  $ With (\let_ ->
             annotated "let expression" $
             position >>>
             swap >>>
             list (
               el (sym "let") >>>
               el (list (
                      el bindingGrammar >>>
                      rest bindingGrammar)) >>>
               el sugaredGrammar) >>>
             let_)

  $ With (\mklit ->
             annotated "literal" $
             position >>>
             swap >>>
             litGrammar >>>
             mklit)

  $ With (\ifp ->
             annotated "if expression" $
             position >>>
             swap >>>
             list (
              el (sym "if") >>>
              el sugaredGrammar >>>
              el sugaredGrammar >>>
              el sugaredGrammar) >>>
             ifp)

  $ With (\mklist ->
            position >>>
            swap >>>
            bracketList (
             rest sugaredGrammar) >>> mklist)

  $ With (\mktuple ->
            position >>>
            swap >>>
            list (
             el (sym "**") >>>
             el sugaredGrammar >>>
             el sugaredGrammar >>>
             rest sugaredGrammar) >>> mktuple)

  $ With (\mkrec ->
             annotated "record literal" $
             position >>>
             swap >>>
             braceList (
               props (
                 restKeys (
                   sugaredGrammar >>>
                   onTail (iso coerce coerce) >>>
                   pair))) >>>
             mkrec)

  $ With (\recprj ->
             annotated "record selection" $
             position >>>
             swap >>>
             list (
               el labelGrammar >>>
               el sugaredGrammar) >>>
             recprj)

  $ With (\recdef ->
             annotated "record selection with default" $
             position >>>
             swap >>>
             list (
               el labelGrammar >>>
               el sugaredGrammar >>>
               el (sym ":default") >>>
               el sugaredGrammar) >>>
             recdef)

  $ With (\recext ->
             annotated "record extension" $
             position >>>
             swap >>>
             list (
               el labelGrammar >>>
               el sugaredGrammar >>>
               el (sym "=") >>>
               el sugaredGrammar) >>>
             recext)

  $ With (\mkvnt ->
             annotated "variant constructor" $
             position >>>
             swap >>>
             ctorLabelGrammar >>>
             mkvnt)

  $ With (\case_ ->
             annotated "case expression" $
             position >>>
             swap >>>
             list (
               el (sym "case") >>>
               el sugaredGrammar >>>
               rest variantMatchLegGrammar) >>>
             case_)

  $ With (\delay ->
             position >>>
             swap >>>
             prefixed Backtick sugaredGrammar >>>
             delay)

  $ With (\force ->
             position >>>
             swap >>>
             list (el sugaredGrammar) >>>
             force)

  $ With (\doblock ->
             annotated "do-block" $
             position >>>
             swap >>>
             list (el (sym "do") >>>
                   el seqStmtGrammar >>>
                   rest seqStmtGrammar >>>
                   onTail cons) >>>
             doblock)

  $ With (\loop ->
             annotated "loop" $
             position >>>
             swap >>>
             list (
               el (sym "loop") >>>
               el (list (
                     el varGrammar >>>
                     rest varGrammar)) >>>
               onTail cons >>>
               el sugaredGrammar) >>>
             loop)

    $ With (\kappa ->
             annotated "kappa expression" $
             position >>>
             swap >>>
             list (
               el (sym "kappa") >>>
               el (list (rest varGrammar)) >>>
               el sugaredGrammar) >>>
             kappa)

    $ With (\catch_ ->
             annotated "catch expression" $
             position >>>
             swap >>>
             list (
               el (sym "catch") >>>
               el sugaredGrammar >>>
               rest variantMatchLegGrammar) >>>
             catch_)

  $ End

----------------------------------------------------------------------
-- Utils

fixG :: Grammar Position (Sexp :- t) (f (Fix f) :- t)
     -> Grammar Position (Sexp :- t) (Fix f :- t)
fixG g = g >>> iso coerce coerce
