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

import Control.Effect.Carrier
import Control.Monad.IO.Class

import qualified Data.ByteString.Lazy.Char8 as BL8
import Data.Functor.Const
import Data.Functor.Foldable (Fix (..))
import qualified Data.Map as M
import Data.Sum
import qualified Data.Text as T
import qualified Language.SexpGrammar

import Eval
import Expr
import Pretty
import Prim.Base
import Prim.Kappa
import Prim.Exception
import Prim.IO
import Prim.Link.Types
import Prim.Record
import Prim.Variant
import Syntax.Sugared
import TypeChecker
import Types

instance PrettyPrim (Const LinkPrim) where
  prettyPrim = \case
    Const Link -> "Link"

instance ( Member (RuntimeErrorEffect) sig
         , Member (EnvEffect v) sig
         , Member (ExceptionEffect v) sig
         , Member (KappaEffect) sig
         , Carrier sig m
         , MonadIO m
         , LambdaValue m :< v
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
                Right sug -> pure (desugar sug :: Expr '[BasePrim, RecordPrim, VariantPrim, IOPrim, KappaPrim, LinkPrim, ExceptionPrim])
              case runInfer (check expr (Fix (T TDouble))) of
                Left tcerror -> evalError $ "Link:\n" ++ render (ppError tcerror)
                Right _ ->
                  pure $ mkVLam @m $ \_ ->
                    localEnv @v (const M.empty) (eval expr)

            _ -> evalError "Link: expected Text"

instance TypePrim (Const LinkPrim) where
  typePrim = \case
    Const Link ->
      forall Star $ \a ->
      mono $
        Fix (T TText) ~>
        Fix (T TUnit) ~>
        a
