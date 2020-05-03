{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE MonoLocalBinds       #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE UndecidableInstances #-}

module Pretty where

import Control.Effect.Reader

import Data.Functor.Const
import Data.Functor.Foldable (Fix(..), para)
import Data.Sum
import Data.Text.Prettyprint.Doc as PP
import Data.Void

import Errors
import Expr
import Types
import Utils

----------------------------------------------------------------------
-- Types

ppLabel :: Label -> Doc ann
ppLabel (Label s) = pretty s

ppKind :: Kind -> Doc ann
ppKind (Arr a@Arr{} b) = parens (ppKind a) <+> "→" <+> ppKind b
ppKind (Arr a b) = ppKind a <+> "→" <+> ppKind b
ppKind Star     = "⋆"
ppKind Row      = "Ω"
ppKind Presence = "Ψ"
ppKind EStar    = "▴"
ppKind EStack   = "Σ"


ppTyVar :: TVar -> Doc ann
ppTyVar (TVar n k) = ppPrefix k <> pretty n
  where
    ppPrefix Arr{}    = "α"
    ppPrefix Star     = "α"
    ppPrefix Row      = "ρ"
    ppPrefix Presence = "ω"
    ppPrefix EStar    = "β"
    ppPrefix EStack   = "τ"

ppMetaVar :: MetaVar -> Doc ann
ppMetaVar (MetaVar n k) = ppPrefix k <> pretty n
  where
    ppPrefix Arr{}    = "'α"
    ppPrefix Star     = "'α"
    ppPrefix Row      = "'ρ"
    ppPrefix Presence = "'ω"
    ppPrefix EStar    = "'β"
    ppPrefix EStack   = "'τ"

ppType :: Type -> Doc ann
ppType = (group .) . para $ \case
  TUnit -> "()"
  TVoid -> "∅"
  TSNil -> "ε"
  TSCons (_,h) (_,t) -> h <+> "::" <+> t

  TEArrow (Fix TSNil,_) (_, b) -> "Dyn⟨" <> b <> "⟩"
  TEArrow (_,a) (_,b) -> "Dyn⟨" <> a <+> "⇒" <+> b <> "⟩"

  TCtor name -> pretty name
  TApp (_,a) (_,b) -> a <+> b
  TRef tv -> ppTyVar tv
  TMeta tv -> ppMetaVar tv
  TForall tv (_,e) -> parens ("∀" <+> ppTyVar tv <> "." <+> e)
  TExists tv (_,e) -> parens ("∃" <+> ppTyVar tv <> "." <+> e)
  TArrow (f',f) (_,a) ->
    case f' of
      Fix (TArrow{}) -> parens f <+> "→" <+> a
      _other         -> f <+>  "→" <+> a

  TRecord (_,row)   -> group $ braces $ space <> align (row <> space)
  TVariant (_,row)  -> group $ angles $ space <> align (row <> space)
  TPresent -> "▪︎"
  TAbsent -> "▫︎"
  TRowEmpty -> "∅"
  TRowExtend lbl (p',_) (f',f) (t',t) ->
    let label = case p' of
          Fix TPresent -> ppLabel lbl
          Fix TAbsent  -> "¬" <> ppLabel lbl
          other        -> ppLabel lbl <> "^" <> ppType other

        field = case (f', p') of
          (Fix TUnit, _) -> label
          (_, Fix TAbsent)   -> label
          _                  -> label <+> ":" <+> f

    in case t' of
         Fix (TRowEmpty) -> field
         Fix (TRef{})    -> field <+> "|" <+> t
         Fix _           -> vsep [ field <> ",", t ]

ppError :: TCError -> Doc ann
ppError (TCError pos reason) =
  vsep [ pretty pos <> ": type check error:"
       , indent 2 $ ppReason reason
       ]

ppReason :: Reason -> Doc ann
ppReason = \case
  CannotUnify t1 t2 -> vsep
    [ "Cannot match expected type with actual type."
    , indent 2 $ "Actual:  " <+> nest 2 (ppType t1)
    , indent 2 $ "Expected:" <+> nest 2 (ppType t2)
    ]
  CannotUnifyLabel lbl t1 t2 -> vsep
    [ "Cannot match label" <+> pretty (show lbl) <+> "in types."
    , indent 2 $ "Actual:  " <+> nest 2 (ppType t1)
    , indent 2 $ "Expected:" <+> nest 2 (ppType t2)
    ]
  CannotUnifyWithSkolem t1 t2 tyvar -> vsep
    [ "Cannot match expected type with actual type, because skolem" <+> ppTyVar tyvar <+> "would escape its scope."
    , indent 2 $ "Actual:  " <+> nest 2 (ppType t1)
    , indent 2 $ "Expected:" <+> nest 2 (ppType t2)
    ]
  InfiniteType t1 -> vsep
    [ "Infinite type:"
    , indent 2 (ppType t1)
    ]
  RecursiveRowType t1 -> vsep
    [ "Recursive row type:"
    , indent 2 (ppType t1)
    ]
  KindMismatch k1 k2 -> vsep
    [ "Kind mismatch:" <+> pretty (show k1) <+> "vs." <+> pretty (show k2)
    ]
  IllKindedType t -> "Ill-kinded type:" <+> pretty (show t)
  VariableNotFound expr -> "Variable not found:" <+> pretty (show expr)
  TypeVariableNotFound tyvar -> "Type variable escaped its scope:" <+> ppTyVar tyvar
  ImpredicativePolymoprhism t -> "Impredicative polymorphism unsupported:" <+> ppType t
  OtherError msg -> pretty msg

----------------------------------------------------------------------
-- Expr

ppVariable :: Variable -> Doc ann
ppVariable (Variable x) = pretty x

class PrettyPrim (p :: * -> *) where
  prettyPrim :: p Void -> Doc ann

instance (Apply PrettyPrim ps) => PrettyPrim (Sum ps) where
  prettyPrim = apply @PrettyPrim prettyPrim

ppExpr :: forall p ann. (PrettyPrim (Sum (Map Const p))) => Expr p -> Doc ann
ppExpr = run . runReader @Int 0 . para alg
  where
    parensIf :: Bool -> Doc ann -> Doc ann
    parensIf = \case
      True -> parens
      False -> id

    alg :: forall m sig. (Member (Reader Int) sig, Carrier sig m) =>
           ExprF p (Expr p, m (Doc ann)) -> m (Doc ann)
    alg = \case
      Ref _ x ->
        pure $ ppVariable x
      Lambda _ x (_, body) -> do
        n <- ask @Int
        body' <- local @Int (const 1) $ body
        pure $ parensIf (n > 1) $ group $ nest 2 $ vsep
          [ "λ" <+> ppVariable x  <> "."
          , group body'
          ]
      App _ (_, f) (_, a) -> do
        n <- ask @Int
        f' <- local @Int (const 2) $ f
        a' <- local @Int (const 3) $ a
        pure $ parensIf (n > 2) $ group $ align $ nest 2 $ vsep [f', group a']
      Let _ x (_, e) (_, b) -> do
        n <- ask @Int
        e' <- local @Int (const 1) $ e
        b' <- local @Int (const 1) $ b
        pure $ parensIf (n > 0) $ group $ align $ vsep
          [ "let" <+> ppVariable x <+> "=" <+> nest 6 (group e')
          , "in" <+> align b'
          ]
      Annot _ (_, b) t -> do
        b' <- local @Int (const 0) b
        pure $ parens (b' <+> ":" <+> ppType t)
      Prim _ p ->
        pure $ prettyPrim p

----------------------------------------------------------------------
-- Values

ppValue :: (Apply Pretty1 v) => Value v -> Doc ann
ppValue (Fix x) = liftPretty ppValue x

----------------------------------------------------------------------

render :: Doc ann -> String
render = show -- FIXME: use proper rendering function
