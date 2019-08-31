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

module IO where

import Control.Monad.IO.Class
import Control.Effect.Carrier
import Control.Effect.Error

import qualified Data.Text as T
import qualified Data.Text.IO as T
import Data.Functor.Const
import Data.Functor.Foldable (Fix (..), unfix)
import Data.Sum

import Expr
import Base
import Utils
import Position

import Types

data IOPrim
  = ReadLn
  | WriteLn

instance ( Member (Error String) sig
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
            _ -> throwError "ReadLn: expected Unit"

      Const WriteLn -> do
        pure $ mkVLam @m $ \c ->
          case projBase c of
            Just (VText t) -> do
              liftIO $ T.putStrLn t
              pure $ mkVUnit
            _ -> throwError "WriteLn: cannot print non-text"

    where
      projBase = project @BaseValue . unfix

ioEff :: Label
ioEff = Label (T.pack "io")

instance TypePrim (Const IOPrim) where
  typePrim = \case
    Const ReadLn ->
      effect $ \e1 ->
      mono $
        (Fix (T TUnit), Fix $ TRowExtend ioEff (Fix TPresent) (Fix (T TUnit)) e1) ~>
        (Fix (T TText))
    Const WriteLn ->
      effect $ \e1 ->
      mono $
        (Fix (T TText), Fix $ TRowExtend ioEff (Fix TPresent) (Fix (T TUnit)) e1) ~>
        (Fix (T TUnit))

----------------------------------------------------------------------

readln :: (IOPrim :<< p, BasePrim :<< p) => Expr p
readln = Fix (Prim dummyPos (inject' ReadLn)) ! prim MkUnit

writeln :: (IOPrim :<< p) => Expr p -> Expr p
writeln x = Fix (Prim dummyPos (inject' WriteLn)) ! x
