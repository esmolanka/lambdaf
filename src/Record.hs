{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}

module Record where

import Control.Effect.Carrier
import Control.Effect.Error

import Data.Functor.Classes
import Data.Functor.Const
import Data.Functor.Foldable (Fix (..), unfix)
import qualified Data.Map as M
import Data.Sum
import qualified Data.Text as T
import Data.Text.Prettyprint.Doc as PP

import Expr
import Position
import Pretty
import Types
import Utils


data RecordPrim
  = RecordNil
  | RecordExtend Label
  | RecordSelect Label
  | RecordDefault Label

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
              map (\(Label lbl, el) -> shows lbl . showString " = " . sp 0 el) lst
      in showString "{" . showBody (M.toList x) . showString "}"

instance Pretty1 RecordValue where
  liftPretty pp = \case
    VRecord x ->
      group $ braces $ align $ vsep $
      punctuate "," $
      map (\(lbl, v) -> ppLabel lbl <+> "=" <+> pp v) (M.toList x)

instance PrettyPrim (Const RecordPrim) where
  prettyPrim = \case
    Const RecordNil           -> "RecordNil"
    Const (RecordExtend lbl)  -> "RecordExtend" <> angles (ppLabel lbl)
    Const (RecordSelect lbl)  -> "RecordSelect" <> angles (ppLabel lbl)
    Const (RecordDefault lbl) -> "RecordDefault" <> angles (ppLabel lbl)

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
            _ -> evalError "RecordExtend: not a record"

      Const (RecordSelect lbl@(Label lbl')) ->
        pure $ mkVLam @m $ \r ->
          case projRecord r of
            Just (VRecord r') ->
              case M.lookup lbl r' of
                Just a  -> pure a
                Nothing -> evalError ("RecordSelect: label not found " ++ show lbl')
            _ -> evalError "RecordSelect: not a record"

      Const (RecordDefault lbl) ->
        pure $ mkVLam @m $ \d ->
        pure $ mkVLam @m $ \r ->
          case projRecord r of
            Just (VRecord r') ->
              case M.lookup lbl r' of
                Just a  -> pure a
                Nothing -> pure d
            _ -> evalError "RecordDefault: not a record"

    where
      projRecord = project @RecordValue . unfix

instance TypePrim (Const RecordPrim) where
  typePrim = \case
    Const RecordNil ->
      mono $ Fix $ TRecord $ Fix $ TRowEmpty
    Const (RecordExtend label) ->
      forall Star $ \a ->
      forall Star $ \b ->
      forall Presence $ \p ->
      forall Row  $ \r ->
      effect $ \e1 ->
      effect $ \e2 ->
      mono $
        (a, e1) ~>
        (Fix $ TRecord $ Fix $ TRowExtend label p b r, e2) ~>
        (Fix $ TRecord $ Fix $ TRowExtend label (Fix TPresent) a r)
    Const (RecordSelect label) ->
      forall Star $ \a ->
      forall Row  $ \r ->
      effect $ \e ->
      mono $ (Fix $ TRecord $ Fix $ TRowExtend label (Fix TPresent) a r, e) ~> a
    Const (RecordDefault label) ->
      forall Star $ \a ->
      forall Presence $ \p ->
      forall Row  $ \r ->
      effect $ \e1 ->
      effect $ \e2 ->
      mono $
      (a, e1) ~> (Fix $ TRecord $ Fix $ TRowExtend label p a r, e2) ~> a

----------------------------------------------------------------------

rnil :: (RecordPrim :<< p) => Expr p
rnil = Fix (Prim dummyPos (inject' RecordNil))

rext :: (RecordPrim :<< p) => String -> Expr p -> Expr p -> Expr p
rext lbl a r = Fix (Prim dummyPos (inject' (RecordExtend (Label (T.pack lbl))))) ! a ! r

rsel :: (RecordPrim :<< p) => String -> Expr p -> Expr p
rsel lbl r = Fix (Prim dummyPos (inject' (RecordSelect (Label (T.pack lbl))))) ! r
