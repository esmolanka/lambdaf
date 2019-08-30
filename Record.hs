{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeOperators              #-}
-- :-/
{-# LANGUAGE UndecidableInstances       #-}

module Record where

import Control.Effect.Carrier
import Control.Effect.Error

import Data.Functor.Classes
import Data.Functor.Const
import Data.Functor.Foldable (Fix (..), unfix)
import qualified Data.Map as M
import Data.Sum

import Expr
import Utils

type Label = String

data RecordPrim
  = RecordNil
  | RecordExtend Label
  | RecordSelect Label

data RecordValue e
  = VRecord (M.Map Label e)

mkVRecord :: (RecordValue :< v) => M.Map Label (Value v) -> Value v
mkVRecord = Fix . inject . VRecord

instance Show1 RecordValue where
  liftShowsPrec sp _sl _n = \case
    VRecord x ->
      let showBody [] = id
          showBody lst =
            foldr1 (\a b -> a . showString ", " . b) $
              map (\(lbl, el) -> showString lbl . showString " = " . sp 0 el) lst
      in showString "{" . showBody (M.toList x) . showString "}"

instance ( Member (Error String) sig
         , Carrier sig m
         , LambdaValue m :< v
         , RecordValue :< v
         ) => EvalPrim m v (Const RecordPrim) where
  evalPrim = \case
      Const RecordNil ->
        pure (mkVRecord M.empty)

      Const (RecordExtend lbl) ->
        pure $ mkVLam @m $ \a ->
        pure $ mkVLam @m $ \r ->
          case projRecord r of
            Just (VRecord r') -> pure $ mkVRecord (M.insert lbl a r')
            _ -> throwError "RecordExtend: not a record"

      Const (RecordSelect lbl) ->
        pure $ mkVLam @m $ \r ->
          case projRecord r of
            Just (VRecord r') ->
              case M.lookup lbl r' of
                Just a  -> pure a
                Nothing -> throwError ("RecordSelect: label not found " ++ lbl)
            _ -> throwError "RecordSelect: not a record"

    where
      projRecord = project @RecordValue . unfix

----------------------------------------------------------------------

rnil :: (RecordPrim :<< p) => Expr p
rnil = Fix (Prim (inject' RecordNil))

rext :: (RecordPrim :<< p) => Label -> Expr p -> Expr p -> Expr p
rext lbl a r = Fix (Prim (inject' (RecordExtend lbl))) ! a ! r

rsel :: (RecordPrim :<< p) => Label -> Expr p -> Expr p
rsel lbl r = Fix (Prim (inject' (RecordSelect lbl))) ! r
