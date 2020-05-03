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

module Prim.IO
  ( IOPrim(..)
  , ioEff
  ) where

import Control.Monad.IO.Class
import Control.Effect.Carrier

import Data.Functor.Const
import Data.Functor.Foldable (Fix (..))
import Data.Sum
import qualified Data.Text as T
import qualified Data.Text.IO as T

import Eval
import Expr
import Prim.Base
import Types
import Utils

data IOPrim
  = ReadLn
  | WriteLn

instance Pretty IOPrim where
  pretty = \case
    ReadLn  -> "ReadLn"
    WriteLn -> "WriteLn"

instance ( Member RuntimeErrorEffect sig
         , Carrier sig m
         , MonadIO m
         , LambdaValue m :< v
         , BaseValue :< v
         ) => EvalPrim m v (Const IOPrim) where
  evalPrim = \case
      Const ReadLn -> do
        pure $ mkVLam @m $ \c ->
          case projBase c of
            Just VUnit -> do
              ln <- liftIO T.getLine
              pure $ mkVText ln
            _ -> evalError "ReadLn: expected Unit"

      Const WriteLn -> do
        pure $ mkVLam @m $ \c ->
          case projBase c of
            Just (VText t) -> do
              liftIO $ T.putStrLn t
              pure $ mkVUnit
            _ -> evalError "WriteLn: cannot print non-text"

ioEff :: Label
ioEff = Label (T.pack "io")

instance (BaseType :<< t) => TypePrim t (Const IOPrim) where
  typePrim = \case
    Const ReadLn ->
      mono $
        Fix TUnit ~> typeCtor BTText
    Const WriteLn ->
      mono $
        typeCtor BTText ~> Fix TUnit
