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

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Prim.Link
  ( LinkPrim(..)
  ) where

import Control.Algebra
import Control.Monad.IO.Class

import qualified Data.ByteString.Lazy.Char8 as BL8
import Data.Fix (Fix (..))
import Data.Functor.Const
import qualified Data.Map as M
import Data.Sum
import qualified Data.Text as T
import qualified Language.SexpGrammar

import Eval
import Expr
import Pretty
import Prim.Base
import Prim.Dyn
import Prim.Exception
import Prim.IO
import Prim.Kappa
import Prim.Link.Types
import Prim.Record
import Prim.Variant
import Syntax.Desugar (desugar)
import Syntax.Grammar (sugaredGrammar)
import TypeChecker
import Types
import Utils

instance Pretty LinkPrim where
  pretty = \case
    Link -> "Link"

instance ( MonadFail m
         , Has (RuntimeErrorEffect) sig m
         , Has (DynEnvEffect v) sig m
         , Has (DynAllocEffect) sig m
         , Has (EnvEffect v) sig m
         , Has (ExceptionEffect v) sig m
         , Has (KappaEffect) sig m
         , Apply Pretty1 v
         , MonadIO m
         , LambdaValue m :< v
         , DynValue :< v
         , BaseValue :< v
         , RecordValue :< v
         , VariantValue :< v
         , KappaValue :< v
         ) => EvalPrim m v (Const LinkPrim) where
  evalPrim = \case
      Const Link -> do
        pure $ mkVLam @m $ \c ->
          case projBase c of
            Just (VText fn) -> do
              src <- liftIO $ BL8.readFile (T.unpack fn)
              expr <- case Language.SexpGrammar.decodeWith sugaredGrammar (T.unpack fn) src of
                Left err -> evalError $ "Link:\n" ++ err
                Right sug -> pure
                  (desugar sug :: Expr
                     '[BaseType, KappaType, DynType, RecordType, VariantType]
                     '[BasePrim, DynPrim, RecordPrim, VariantPrim, IOPrim, KappaPrim, LinkPrim, ExceptionPrim]
                  )
              case runInfer @[BaseType, KappaType, DynType, RecordType, VariantType] (check expr (typeCtor BTFloat)) of
                Left tcerror -> evalError $ "Link:\n" ++ render (ppError tcerror)
                Right _ ->
                  pure $ mkVLam @m $ \_ ->
                    localEnv @v (const M.empty) (eval expr)

            _ -> evalError "Link: expected Text"

instance (BaseType :<< t) => TypePrim t (Const LinkPrim) where
  typePrim = \case
    Const Link ->
      forall Star $ \a ->
      mono $
        typeCtor BTText ~>
        Fix TUnit ~>
        a
