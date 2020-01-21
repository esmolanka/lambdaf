module Errors where

import Types
import Expr
import Syntax.Position

data TCError = TCError Position Reason
  deriving (Show)

data Reason
  = CannotUnify Type Type
  | CannotUnifyLabel Label Type Type
  | InfiniteType Type
  | RecursiveRowType Type
  | KindMismatch Kind Kind
  | ImpredicativePolymoprhism Type
  | IllKindedType (TypeF Kind)
  | VariableNotFound Variable
  | TypeVariableNotFound TVar
  | OtherError String
  deriving (Show)
