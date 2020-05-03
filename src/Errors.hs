module Errors where

import Types
import Expr
import Syntax.Position

data TCError t = TCError Position (Reason t)

data Reason t
  = CannotUnify (Type t) (Type t)
  | CannotUnifyLabel Label (Type t) (Type t)
  | CannotUnifyWithSkolem (Type t) (Type t) TVar
  | InfiniteType (Type t)
  | RecursiveRowType (Type t)
  | KindMismatch Kind Kind
  | ImpredicativePolymoprhism (Type t)
  | IllKindedType (TypeF t Kind)
  | VariableNotFound Variable
  | TypeVariableNotFound TVar
  | OtherError String
