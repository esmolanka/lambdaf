module Errors where

import Types
import Syntax.Position

data TCError = TCError Position Reason
  deriving (Show)

data Reason
  = CannotUnify Type Type
  | CannotUnifyLabel Label Type Type
  | InfiniteType Type
  | RecursiveRowType Type
  | KindMismatch Kind Kind
  | IllKindedType (TypeF Kind)
  | VariableNotFound String -- TODO: replace to variable
  deriving (Show)
