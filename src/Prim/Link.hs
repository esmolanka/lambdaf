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

module Prim.Link
  ( module Prim.Link
  , module Prim.Link.Types
  ) where

import Control.Effect.Carrier
import Control.Effect.State
import Control.Effect.Reader
import Control.Effect.Error
import Control.Monad.IO.Class

import Data.Functor.Const
import Data.Functor.Foldable (Fix (..), unfix)
import Data.Sum
import qualified Data.Map as M
import qualified Data.ByteString.Lazy.Char8 as BL8
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import qualified Data.Text.IO as T

import qualified Language.SexpGrammar

import Expr
import Pretty
import Prim.Base
import Prim.IO
import Prim.Record
import Prim.Anf
import Prim.Link.Types
import Syntax.Position
import Syntax.Sugared
import Types
import TypeChecker
import Utils

instance PrettyPrim (Const LinkPrim) where
  prettyPrim = \case
    Const (Link t) -> "Link" <> ppType t

instance ( Member (Error String) sig
         , Member (State EVar) sig
         , Member (Reader (M.Map Variable (Value v))) sig
         , Carrier sig m
         , MonadIO m
         , LambdaValue m :< v
         , BaseValue :< v
         , RecordValue :< v
         , AnfValue :< v
         ) => EvalPrim m v (Const LinkPrim) where
  evalPrim = \case
      Const (Link t) -> do
        pure $ mkVLam @m $ \c ->
          case projBase c of
            Just (VText fn) -> do
              src <- liftIO $ BL8.readFile (T.unpack fn)
              expr <- case Language.SexpGrammar.decodeWith sugaredGrammar (T.unpack fn) src of
                Left err -> evalError $ "Link:\n" ++ err
                Right sug -> pure (desugar sug :: Expr '[BasePrim, RecordPrim, AnfPrim, IOPrim, LinkPrim])
              case runInfer (inferExprType expr) of
                Left tcerror -> evalError $ "Link:\n" ++ render (ppError tcerror)
                Right (t', e')
                  | t == t' ->
                    pure $ mkVLam @m $ \_ ->
                      local @(M.Map Variable (Value v)) (const M.empty) (eval expr)
                  | otherwise -> evalError "Link: types did not match."

            _ -> evalError "ReadLn: expected Unit"

    where
      projBase = project @BaseValue . unfix


instance TypePrim (Const LinkPrim) where
  typePrim = \case
    Const (Link t) ->
      effect $ \e1 ->
      effect $ \e2 ->
      mono $
        (Fix (T TText), Fix $ TRowExtend ioEff (Fix TPresent) (Fix (T TUnit)) e1) ~>
        (Fix (T TUnit), e2) ~>
        t
