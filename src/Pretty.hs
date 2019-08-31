{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}

module Pretty where

import Data.Functor.Foldable (Fix(..), para)
import Data.String

import Data.Text.Prettyprint.Doc as PP

import Types
import Errors

ppTyVar :: TyVar -> Doc ann
ppTyVar (TyVar n k) = ppKind k <> pretty n
  where
    ppKind Star     = "α"
    ppKind Row      = "ρ"
    ppKind Presence = "ω"
    ppKind EStar    = "β"

ppBaseType :: BaseType -> Doc ann
ppBaseType = fromString . drop 1 . show

ppAnfType :: EType -> Doc ann
ppAnfType = fromString . drop 1 . show

ppType :: Type -> Doc ann
ppType = (group .) . para $ \case
  T c -> ppBaseType c
  TE c -> ppAnfType c
  TExpr (_, t) -> "Expr" <+> t
  TVar tv -> ppTyVar tv
  TArrow (f',f) (_,e) (_,a) ->
    case f' of
      Fix (TArrow{}) -> parens f <+> "-⟨" <> group e <> "⟩->" <+> a
      _other         -> f <+>  "-⟨" <> group e <> "⟩->" <+> a

  TPair (_,a) (_,b) -> a <+> "**" <+> b
  TRecord (_,row)   -> group $ braces $ space <> align (row <> space)
  TVariant (_,row)  -> group $ angles $ space <> align (row <> space)
  TPresent -> "▪︎"
  TAbsent -> "▫︎"
  TRowEmpty -> "∅"
  TRowExtend (Label lbl) (p',_) (f',f) (t',t) ->
    let label = case p' of
          Fix TPresent -> pretty lbl
          Fix TAbsent  -> "¬" <> pretty lbl
          other        -> pretty lbl <> "‹" <> ppType other <> "›"

        field = case (f', p') of
          (Fix (T TUnit), _) -> label
          (_, Fix TAbsent)   -> label
          _                  -> label <+> ":" <+> f

    in case t' of
         Fix (TRowEmpty) -> field
         Fix (TVar{})    -> field <+> "|" <+> t
         Fix _           -> vsep [ field <> ",", t ]

ppError :: TCError -> Doc ann
ppError (TCError pos reason) =
  vsep [ pretty (show pos) <> ": type check error:"
       , indent 2 $ ppReason reason
       ]

ppReason :: Reason -> Doc ann
ppReason = \case
  CannotUnify t1 t2 -> vsep
    [ "Cannot unify types."
    , indent 2 $ "Actual:  "   <+> nest 2 (ppType t1)
    , indent 2 $ "Expected:" <+> nest 2 (ppType t2)
    ]
  CannotUnifyLabel lbl t1 t2 -> vsep
    [ "Cannot unify label" <+> pretty (show lbl) <+> "in types."
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
    [ "Kind mismatch:" <+> pretty (show k1) <+> "!~" <+> pretty (show k2)
    ]
  IllKindedType _ -> "Ill-kinded type"
  VariableNotFound expr -> "Variable not found:" <+> pretty (show expr)

pp :: Doc ann -> String
pp = show
