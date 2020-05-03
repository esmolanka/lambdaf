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

module Prim.Record where

import Control.Effect.Carrier

import Data.Functor.Const
import Data.Functor.Foldable (Fix (..), unfix)
import qualified Data.Map as M
import Data.Sum
import Data.Text.Prettyprint.Doc as PP

import Expr
import Eval
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

instance Pretty1 RecordValue where
  liftPretty pp = \case
    VRecord x ->
      group $ align $
      enclose (lbrace <> space) (line <> rbrace) $ vcat $
      zipWith (<>)
        (mempty : repeat (comma <> space))
        (map (\(lbl, v) -> nest 4 $ vsep [ppLabel lbl <+> "=", pp v]) (M.toList x))

instance Pretty RecordPrim where
  pretty = \case
    RecordNil         -> "RecordNil"
    RecordExtend lbl  -> "RecordExtend" <> angles (ppLabel lbl)
    RecordSelect lbl  -> "RecordSelect" <> angles (ppLabel lbl)
    RecordDefault lbl -> "RecordDefault" <> angles (ppLabel lbl)

instance ( Member RuntimeErrorEffect sig
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

instance TypePrim t (Const RecordPrim) where
  typePrim = \case
    Const RecordNil ->
      mono $ Fix $ TRecord $ Fix $ TRowEmpty
    Const (RecordExtend label) ->
      forall Star $ \a ->
      forall Star $ \b ->
      forall Presence $ \p ->
      forall Row  $ \r ->
      mono $
        a ~>
        (Fix $ TRecord $ Fix $ TRowExtend label p b r) ~>
        (Fix $ TRecord $ Fix $ TRowExtend label (Fix TPresent) a r)
    Const (RecordSelect label) ->
      forall Star $ \a ->
      forall Row  $ \r ->
      mono $
        (Fix $ TRecord $ Fix $ TRowExtend label (Fix TPresent) a r) ~> a
    Const (RecordDefault label) ->
      forall Star $ \a ->
      forall Presence $ \p ->
      forall Row  $ \r ->
      mono $
        a ~> (Fix $ TRecord $ Fix $ TRowExtend label p a r) ~> a
