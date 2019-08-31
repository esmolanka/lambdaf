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

module Sugared where

import Prelude hiding (id)

import Control.Arrow (first)
import Control.Category (id, (>>>))
import Control.Monad.Free
import Control.Effect.Reader
import Control.Effect.Pure

import Data.Coerce
import Data.Functor.Foldable (Fix(..), cata, futu)
import qualified Data.Map as M
import Data.Proxy
-- import Data.Sum
import Data.Text (Text, pack, isPrefixOf)
import GHC.Generics

import Language.Sexp.Located (Position(..))
-- import qualified Language.SexpGrammar as S
import Language.SexpGrammar
import Language.SexpGrammar.Generic

import qualified Expr as Raw
import qualified Base as Raw
import qualified Record as Raw
import qualified IO as Raw
-- import qualified Anf as Raw
import qualified Position as Raw
import Expr (Variable(..))
import Types
import Utils

data Literal
  = LitDbl  Double
  | LitStr  Text
  | LitUnit
    deriving (Generic)

data LetBinding e
  = OrdinaryBinding Variable e
  {- | RecursiveBinding Variable Variable [Variable] e -}
    deriving (Generic)

data SeqBinding e
  = IgnoringBinding e
  | OrdinarySeqBinding Variable e
    deriving (Generic)

type Sugared = Fix SugaredF
data SugaredF e
  = Var     Position Variable
  | Lambda  Position Variable [Variable] e
  | App     Position e e [e]
  | Let     Position (LetBinding e) [(LetBinding e)] e
  | Literal Position Literal
  | If      Position e e e
  -- | MkList  Position [e]
  | MkRec   Position [(Label, e)]
  | RecProj Position Label e
  | RecExt  Position Label e e
  | Delay   Position e
  | Force   Position e
  | DoBlock Position [SeqBinding e]
    deriving (Generic)

dsPos :: Position -> Raw.Position
dsPos (Position fn l c) = Raw.Position (pack fn) l c l c

desugar :: forall p. (Raw.BasePrim :<< p, Raw.RecordPrim :<< p, Raw.IOPrim :<< p) => Sugared -> Raw.Expr p
desugar = resolvePrimitives . futu coalg
  where
    dummyVar = Variable "_"

    mkLambda pos bindings e =
      foldr (\b' rest_ -> Free $ Raw.Lambda pos b' rest_) e bindings

    mkApp pos f args =
      foldl (\acc arg -> Free $ Raw.App pos acc arg) f args

    coalg :: Sugared -> Raw.ExprF p (Free (Raw.ExprF p) Sugared)
    coalg = \case
      Fix (Var pos var)       -> Raw.Ref (dsPos pos) var

      Fix (Lambda pos b bs e) -> let Free x = mkLambda (dsPos pos) (b:bs) (Pure e) in x

      Fix (App pos f a as)    -> let Free x = mkApp (dsPos pos) (Pure f) (map Pure (a:as)) in x

      Fix (Let pos b bs e) ->
        let (name, expr) = desugarBinding b
        in Raw.Let (dsPos pos) name expr
             (foldr (\(x, a) rest_ -> Free $ Raw.Let (dsPos pos) x a rest_) (Pure e) (map desugarBinding bs))
        where
          desugarBinding :: LetBinding Sugared -> (Variable, Free (Raw.ExprF p) Sugared)
          desugarBinding = \case
            OrdinaryBinding n expr -> (n, Pure expr)
            -- RecursiveBinding n var vars expr -> (n, Raw.LetBinding, body)
            --   where
            --     avs = map (const dummyVar) (var:vars)
            --     refs = reverse $ zipWith (\var n -> Free $ Raw.Var pos var n) avs [0..]
            --     body = mkLambda pos avs $ mkApp pos fixpoint (innerBody:refs)
            --     fixpoint = Free $ Raw.Const pos Raw.Fixpoint
            --     innerBody = mkLambda pos (n:var:vars) (Pure expr)

      Fix (Literal pos lit) ->
        case lit of
          LitDbl  x -> Raw.Prim (dsPos pos) (inject' (Raw.MkDouble x))
          LitStr  x -> Raw.Prim (dsPos pos) (inject' (Raw.MkText x))
          LitUnit   -> Raw.Prim (dsPos pos) (inject' Raw.MkUnit)

      Fix (If pos cond tr fls) ->
        let Free x =
              mkApp (dsPos pos) (Free $ Raw.Prim (dsPos pos) (inject' Raw.If))
                [ Pure cond
                , mkLambda (dsPos pos) [dummyVar] (Pure tr)
                , mkLambda (dsPos pos) [dummyVar] (Pure fls)
                ]
        in x

      Fix (MkRec pos elems) ->
        let empty = Raw.Prim (dsPos pos) (inject' Raw.RecordNil)
            ext lbl p r = Raw.App (dsPos pos) (Free (Raw.App (dsPos pos) (Free (Raw.Prim (dsPos pos) (inject' (Raw.RecordExtend lbl)))) p)) r
        in case foldr (\(lbl, e) rest_ -> Free $ ext lbl (Pure e) rest_) (Free empty) elems of
             Free x -> x
             Pure{} -> error "Woot"

      Fix (RecProj pos label record) ->
        Raw.App (dsPos pos)
          (Free (Raw.Prim (dsPos pos) (inject' (Raw.RecordSelect label))))
          (Pure record)

      Fix (RecExt pos label record payload) ->
        Raw.App (dsPos pos)
          (Free (Raw.App (dsPos pos) (Free (Raw.Prim (dsPos pos) (inject' (Raw.RecordExtend label)))) (Pure payload)))
          (Pure record)

      Fix (Delay pos expr) ->
        Raw.App (dsPos pos)
          (Free (Raw.Prim (dsPos pos) (inject' Raw.Delay)))
          (Free (Raw.Lambda (dsPos pos) (Variable "_") (Pure expr)))

      Fix (Force pos expr) ->
        Raw.App (dsPos pos)
          (Pure expr)
          (Free (Raw.Prim (dsPos pos) (inject' Raw.MkUnit)))

      Fix (DoBlock pos stmts) ->
        let -- mkForce p a = Free (Raw.App p (Pure a) (Free (Raw.Prim p (inject' Raw.MkUnit))))
            mkSeq p x a b = Free (Raw.App (dsPos p) (Free (Raw.Lambda (dsPos p) x b)) (Pure a))
        in
        case stmts of
          [] -> error "Impossible empty do-block"
          (_:_) ->
            let bind bnd rest_ =
                  let (var, expr) = case bnd of
                        IgnoringBinding e -> (dummyVar, e)
                        OrdinarySeqBinding x e -> (x, e)
                  in mkSeq pos var expr rest_
                block = foldr bind
                  (case last stmts of
                      IgnoringBinding e -> mkSeq pos dummyVar e (Free (Raw.Ref (dsPos pos) dummyVar))
                      OrdinarySeqBinding x e -> mkSeq pos x e (Free (Raw.Ref (dsPos pos) x))) (init stmts)
            in case block of
                 Free x -> x
                 Pure{} -> error "Impossible pure"



primitives :: (Raw.BasePrim :<< p, Raw.IOPrim :<< p) => proxy p -> M.Map Variable (Int, Sum' p)
primitives _ = M.fromList
  [ (Variable "+",     (0, inject' Raw.Add))
  , (Variable "readnum", (0, inject' Raw.ReadDouble))
  , (Variable "readln", (0, inject' Raw.ReadLn))
  , (Variable "writeln", (0, inject' Raw.WriteLn))
  ]

resolvePrimitives :: forall p. (Raw.BasePrim :<< p, Raw.IOPrim :<< p) => Raw.Expr p -> Raw.Expr p
resolvePrimitives expr = run . runReader (primitives (Proxy @p)) $ (cata alg expr)
  where
    alg :: forall r. (r ~ M.Map Variable (Int, Sum' p)) => Raw.ExprF p (ReaderC r PureC (Raw.Expr p)) -> ReaderC r PureC (Raw.Expr p)
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
    parseVar t =
      if t `elem` ["lambda","let","if","record","delay","do","=","?","tt","ff"] ||
         ":" `isPrefixOf` t
      then Left (unexpected t)
      else Right (Variable t)


labelGrammar :: Grammar Position (Sexp :- t) (Label :- t)
labelGrammar = keyword >>> iso coerce coerce


bindingGrammar :: Grammar Position (Sexp :- t) (LetBinding Sugared :- t)
bindingGrammar = match
  $ With (\ordinary ->
            bracketList (
             el varGrammar >>>
             el sugaredGrammar) >>>
            ordinary)
  -- $ With (\recursive ->
  --           bracketList (
  --            el (sym ":rec") >>>
  --            el varGrammar >>>
  --            el (list (el varGrammar >>> rest varGrammar)) >>>
  --            el sugaredGrammar) >>>
  --           recursive)
  $ End


seqStmtGrammar :: Grammar Position (Sexp :- t) (SeqBinding Sugared :- t)
seqStmtGrammar = match
  $ With (\ign -> sugaredGrammar >>> ign)
  $ With (\bnd -> braceList (
             el varGrammar >>>
             el (sym "<-") >>>
             el sugaredGrammar
             ) >>> bnd)
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
  $ With (\litd -> double >>> litd)
  $ With (\lits -> string  >>> lits)
  $ With (\litu -> list id >>> litu)
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

  -- $ With (\mklst ->
  --            annotated "list literal" $
  --            position >>>
  --            swap >>>
  --            bracketList (rest sugaredGrammar) >>>
  --            mklst)

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

  $ With (\recext ->
             annotated "record extension" $
             position >>>
             swap >>>
             list (
               el labelGrammar >>>
               el sugaredGrammar >>>
               el (sym ":extend") >>>
               el sugaredGrammar) >>>
             recext)

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

  $ End

----------------------------------------------------------------------
-- Utils

fixG :: Grammar Position (Sexp :- t) (f (Fix f) :- t)
     -> Grammar Position (Sexp :- t) (Fix f :- t)
fixG g = g >>> iso coerce coerce
