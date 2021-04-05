{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}

module Syntax.Sugared where

import Prelude hiding (id)

import Data.Fix (Fix (..))
import Data.Text (Text)
import GHC.Generics
import Language.Sexp.Located (Position(..))

import Expr (Variable(..))
import Types

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
  | MkRec   Position [(Label, e)] (Maybe e)
  | RecProj Position Label e
  | RecDef  Position Label e e
  | MkVnt   Position Label
  | Case    Position e [VariantMatchLeg e]
  | Delay   Position e
  | Force   Position e
  | DoBlock Position [SeqBinding e]
  | Loop    Position [Variable] e
  | Catch   Position e [VariantMatchLeg e]
  | Prev    Position e
    deriving (Generic)
