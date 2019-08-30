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

import qualified Data.Text.IO as T
import Data.Functor.Const
import Data.Functor.Foldable (Fix (..), unfix)
import Data.Sum

import Expr
import Base
import Utils

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
        ln <- liftIO T.getLine
        pure $ mkVText ln

      Const WriteLn -> do
        pure $ mkVLam @m $ \c ->
         case projBase c of
           Just (VText t) -> do
             liftIO $ T.putStrLn t
             pure $ mkVUnit
           _ -> throwError "WriteLn: cannot print non-text"

    where
      projBase = project @BaseValue . unfix

----------------------------------------------------------------------

readln :: (IOPrim :<< p) => Expr p
readln = Fix (Prim (inject' ReadLn))

writeln :: (IOPrim :<< p) => Expr p -> Expr p
writeln x = Fix (Prim (inject' WriteLn)) ! x
