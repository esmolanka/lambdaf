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

module Syntax.Grammar (sugaredGrammar) where

import Prelude hiding (id)

import Control.Category (id)

import Data.Char (isUpper)
import Data.Coerce
import Data.Fix (Fix (..))
import Data.Text (Text, uncons)

import Language.SexpGrammar
import Language.SexpGrammar.Generic

import Expr (Variable(..))
import Types
import Syntax.Sugared

----------------------------------------------------------------------
-- Grammars

reservedWords :: [Text]
reservedWords =
  [ "lambda", "let", "if", "case", "catch", "prev"
  , "do", "loop", "=", "<-", "**", "tt", "ff"
  ]

{-# NOINLINE varGrammar #-}
varGrammar :: Grammar Position (Sexp :- t) (Variable :- t)
varGrammar =
  symbol >>>
  partialOsi parseVar coerce
  where
    parseVar :: Text -> Either Mismatch Variable
    parseVar t
      | t `elem` reservedWords = Left (unexpected t)
      | Just (h, _) <- uncons t, h == ':' || isUpper h = Left (unexpected t)
      | otherwise = Right (Variable t)

{-# NOINLINE ctorLabelGrammar #-}
ctorLabelGrammar :: Grammar Position (Sexp :- t) (Label :- t)
ctorLabelGrammar =
  symbol >>>
  partialOsi parseCtor coerce
  where
    parseCtor :: Text -> Either Mismatch Label
    parseCtor t
      | Just (h, _) <- uncons t, isUpper h = Right (Label t)
      | otherwise = Left (unexpected t)


{-# NOINLINE labelGrammar #-}
labelGrammar :: Grammar Position (Sexp :- t) (Label :- t)
labelGrammar = keyword >>> iso coerce coerce


{-# NOINLINE bindingGrammar #-}
bindingGrammar :: Grammar Position (Sexp :- t) (LetBinding Sugared :- t)
bindingGrammar = with $ \bnd ->
  bracketList (
    el varGrammar >>>
    el sugaredGrammar) >>>
  bnd


{-# NOINLINE seqStmtGrammar #-}
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


{-# NOINLINE variantMatchLegGrammar #-}
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


{-# NOINLINE boolGrammar #-}
boolGrammar :: Grammar Position (Sexp :- t) (Bool :- t)
boolGrammar = symbol >>> partialOsi
  (\case
      "tt" -> Right True
      "ff" -> Right False
      other -> Left $ expected "bool" <> unexpected ("symbol " <> other))
  (\case
      True -> "tt"
      False -> "ff")


{-# NOINLINE litGrammar #-}
litGrammar :: Grammar Position (Sexp :- t) (Literal :- t)
litGrammar = match
  $ With (\litb -> boolGrammar >>> litb)
  $ With (\litf -> double      >>> litf)
  $ With (\lits -> string      >>> lits)
  $ With (\litu -> list id     >>> litu)
  $ End


{-# NOINLINE sugaredGrammar #-}
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

    $ With (\catch_ ->
             annotated "catch expression" $
             position >>>
             swap >>>
             list (
               el (sym "catch") >>>
               el sugaredGrammar >>>
               rest variantMatchLegGrammar) >>>
             catch_)

    $ With (\prev ->
             annotated "prev expression" $
             position >>>
             swap >>>
             list (
               el (sym "prev") >>>
               el sugaredGrammar) >>>
             prev)

  $ End

----------------------------------------------------------------------
-- Utils

fixG :: Grammar Position (Sexp :- t) (f (Fix f) :- t)
     -> Grammar Position (Sexp :- t) (Fix f :- t)
fixG g = g >>> iso coerce coerce
