{-# LANGUAGE ConstraintKinds      #-}
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

import Control.Category ((>>>))
import Control.Effect.Reader
import Control.Carrier.Reader

import Data.Functor.Classes
import Data.Fix (Fix(..))
import Data.Functor.Foldable (para)
import Data.Sum
import qualified Data.Text as T
import Data.Text.Prettyprint.Doc
import qualified Data.Text.Prettyprint.Doc.Render.Text as ToText
import Data.Void

import Errors
import Expr
import Types
import Utils

----------------------------------------------------------------------
-- Types

class PrettyType (t :: * -> *) where
  prettyCtor :: t Void -> Doc ann

  prettySpine :: forall ann. Int -> (t Void, [Int -> Doc ann]) -> Maybe (Doc ann)
  prettySpine _ _ = Nothing

instance (Apply PrettyType ts) => PrettyType (Sum ts) where
  prettyCtor = apply @PrettyType prettyCtor
  prettySpine lvl (n, args) = apply @PrettyType (\a -> prettySpine lvl (a, args)) n

ppLabel :: Label -> Doc ann
ppLabel (Label s) = pretty s

ppKind :: Kind -> Doc ann
ppKind (Arr a@Arr{} b) = parens (ppKind a) <+> "→" <+> ppKind b
ppKind (Arr a b) = ppKind a <+> "→" <+> ppKind b
ppKind Star     = "⋆"
ppKind Row      = "Ω"
ppKind Presence = "Ψ"
ppKind EStar    = "⊛"
ppKind Region   = "Ξ"

ppTyVar :: TVar -> Doc ann
ppTyVar (TVar n k) = ppPrefix k <> pretty n
  where
    ppPrefix Arr{}    = "α"
    ppPrefix Star     = "α"
    ppPrefix Row      = "ρ"
    ppPrefix Presence = "ω"
    ppPrefix EStar    = "β"
    ppPrefix Region   = "σ"

ppMetaVar :: MetaVar -> Doc ann
ppMetaVar (MetaVar n k) = ppPrefix k <> pretty n
  where
    ppPrefix Arr{}    = "'α"
    ppPrefix Star     = "'α"
    ppPrefix Row      = "'ρ"
    ppPrefix Presence = "'ω"
    ppPrefix EStar    = "'β"
    ppPrefix Region   = "'σ"

parensIf :: Bool -> Doc ann -> Doc ann
parensIf True = parens
parensIf False = id

ppType :: forall t ann. (Apply' PrettyType t) => Type t -> Doc ann
ppType = ppType' 0

ppType' :: forall t ann. (Apply' PrettyType t) => Int -> Type t -> Doc ann
ppType' lvl = spine >>> \case
  (Fix (TCtor name), rest) | Just doc <- prettySpine lvl (name, map (\x n -> ppType' n x) rest) ->
    doc
  (Fix otherTyCon, []) ->
    ppTypeCon lvl otherTyCon
  (Fix otherTyCon, rest) ->
    parensIf (lvl > 1) $ group $ nest 2 $ hsep (ppTypeCon 1 otherTyCon : map (ppType' 2) rest)

  where
    ppTypeCon :: Int -> TypeF t (Type t) -> Doc ann
    ppTypeCon lvl = \case
      TUnit      -> "unit"
      TVoid      -> "void"
      TRef tv    -> ppTyVar tv
      TMeta tv   -> ppMetaVar tv

      TArrow a b ->
        parensIf (lvl > 0) $ group $ nest 2 $ ppType' 1 a <> line <> "→" <+> ppType' 0 b

      TForall tv e  -> parensIf (lvl > 0) ("∀" <+> ppTyVar tv <> "." <+> ppType' 0 e)
      TExists tv e  -> parensIf (lvl > 0) ("∃" <+> ppTyVar tv <> "." <+> ppType' 0 e)

      TCtor name    -> prettyCtor name

      TApp _ _      -> error "Impossible"

      TPresent      -> "+"
      TAbsent       -> "-"
      TRowEmpty     -> "∅"

      TRowExtend lbl p' f' t' -> parensIf (lvl > 0) $
        let label = case p' of
              Fix TPresent -> ppLabel lbl
              Fix TAbsent  -> "¬" <> ppLabel lbl
              other        -> ppLabel lbl <> "^" <> ppType other

            field = case (f', p') of
              (Fix TUnit, _) -> label
              (_, Fix TAbsent)   -> label
              _                  -> label <+> ":" <+> ppType' 0 f'

        in case t' of
             Fix (TRowEmpty) -> field
             Fix (TRef{})    -> field <+> "|" <+> ppType' 0 t'
             Fix (TMeta{})   -> field <+> "|" <+> ppType' 0 t'
             Fix _           -> vsep [ field <> ",", ppType' 0 t' ]

----------------------------------------------------------------------
-- Errors

ppError :: (Apply' PrettyType t, Show1 (TypeF t)) => TCError t -> Doc ann
ppError (TCError pos reason) =
  vsep [ pretty pos <> ": type check error:"
       , indent 2 $ ppReason reason
       ]

ppReason :: (Apply' PrettyType t, Show1 (TypeF t)) => Reason t -> Doc ann
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
  IllKindedType t -> "Ill-kinded type:" <+> pretty (liftShowsPrec showsPrec showList 0 t "")
  VariableNotFound var -> "Variable not found:" <+> squotes (ppVariable var)
  TypeVariableNotFound tyvar -> "Type variable escaped its scope:" <+> ppTyVar tyvar
  ImpredicativePolymoprhism t -> "Impredicative polymorphism unsupported:" <+> ppType t
  OtherError msg -> pretty msg

----------------------------------------------------------------------
-- Expr

ppVariable :: Variable -> Doc ann
ppVariable (Variable x) = pretty x

ppExpr :: forall t p ann. (Apply' Pretty1 p, Apply' PrettyType t) => Expr t p -> Doc ann
ppExpr = run . runReader @Int 0 . para alg
  where
    parensIf :: Bool -> Doc ann -> Doc ann
    parensIf = \case
      True -> parens
      False -> id

    alg :: forall m sig. (Has (Reader Int) sig m) =>
           ExprF t p (Expr t p, m (Doc ann)) -> m (Doc ann)
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
        pure $ liftPretty absurd p

----------------------------------------------------------------------
-- Values

ppValue :: (Pretty1 (Sum v)) => Value v -> Doc ann
ppValue (Fix x) = liftPretty ppValue x

----------------------------------------------------------------------

render :: Doc ann -> String
render =
  T.unpack . ToText.renderStrict . layoutSmart defaultLayoutOptions

renderDoc :: Doc ann -> T.Text
renderDoc =
  ToText.renderStrict . layoutSmart defaultLayoutOptions
