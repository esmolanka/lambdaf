{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase       #-}

module KappaInterpreter where

import Control.Monad
import Control.Monad.IO.Class

import Control.Effect
import Control.Effect.Error
import Control.Effect.Reader

import Data.Map (Map)
import qualified Data.Map as M

data EPrim
  = EId
  | ELit Double
  | EVec [Double]
  | EAdd
  | EMul
  | ESub
  | EDiv
  | EPrint
  deriving (Show)

data EPrim1
  = EFold
  deriving (Show)

newtype EVar = EVar Int
  deriving (Show, Ord, Eq)

data EExpr
  = ERef   EVar
  | EComp  EExpr EExpr
  | EKappa EVar EExpr
  | ELoop  EExpr
  | EPrim  EPrim
  | EPrim1 EPrim1 EExpr
    deriving (Show)

newtype Stack = Stack [Value]
  deriving (Show)

push :: Value -> Stack -> Stack
push x (Stack xs) = Stack (x : xs)

pop :: Stack -> (Value, Stack)
pop (Stack (x : xs)) = (x, Stack xs)
pop (Stack []) = (VUnit, Stack [])

data Value
  = VDouble Double
  | VVector [Double]
  | VUnit
    deriving (Show)

newtype Env = Env (Map EVar Value)
  deriving (Show)

at :: EVar -> Env -> Value
at x (Env m) = M.findWithDefault VUnit x m

with :: (Member (Reader Env) sig, Carrier sig m) => EVar -> Value -> m a -> m a
with x val = local (\(Env vals) -> Env (M.insert x val vals))

eval :: forall m sig.
  ( Member (Reader Env) sig
  , Member (Error String) sig
  , MonadIO m
  , Carrier sig m
  ) => EExpr -> Stack -> m Stack
eval e stk = case e of
  ERef x ->
    push <$> (at x <$> ask) <*> pure stk

  EComp f g ->
    eval f stk >>= \stk' -> eval g stk'

  EKappa x f ->
    let (val, stk') = pop stk
    in with x val (eval f stk')

  ELoop f -> snd . pop <$> eval f (push VUnit stk)

  EPrim p ->
    case p of
      ELit n ->
        pure $ push (VDouble n) stk

      EVec xs ->
        pure $ push (VVector xs) stk

      EId ->
        pure stk

      EAdd ->
        let (a, stk') = pop stk
            (b, stk'') = pop stk'
        in case (a, b) of
             (VDouble a', VDouble b') -> pure $ push (VDouble (a' + b')) stk''
             _ -> throwError $ "Wrong arguments for Add: " ++ show (a, b)

      EMul ->
        let (a, stk') = pop stk
            (b, stk'') = pop stk'
        in case (a, b) of
             (VDouble a', VDouble b') -> pure $ push (VDouble (a' * b')) stk''
             _ -> throwError $ "Wrong arguments for Mul: " ++ show (a, b)

      ESub ->
        let (a, stk') = pop stk
            (b, stk'') = pop stk'
        in case (a, b) of
             (VDouble a', VDouble b') -> pure $ push (VDouble (a' - b')) stk''
             _ -> throwError $ "Wrong arguments for Sub: " ++ show (a, b)

      EDiv ->
        let (a, stk') = pop stk
            (b, stk'') = pop stk'
        in case (a, b) of
             (VDouble a', VDouble b') -> pure $ push (VDouble (a' / b')) stk''
             _ -> throwError $ "Wrong arguments for Div: " ++ show (a, b)

      EPrint ->
        let (a, stk') = pop stk
        in stk' <$ liftIO (putStrLn $ "OUT: " ++ show a)

  EPrim1 p k ->
    case p of
      EFold ->
        let (vec, stk') = pop stk
        in case vec of
             VVector xs -> foldM (\stk'' x -> eval k (push (VDouble x) stk'')) stk' xs
             _ -> throwError $ "Wrong arguments for Fold"


runEval :: ErrorC String (ReaderC Env (LiftC IO)) a -> IO (Either String a)
runEval = runM . runReader (Env mempty) . runError

go :: EExpr -> IO (Either String Stack)
go k = runEval (eval k (Stack []))

(>>>) = EComp
infixr 4 >>>

-- >>> go $ EPrim (ELit 0) >>> EPrim (EVec [1.0,2.0,3.0]) >>> EPrim1 EFold (EPrim EAdd)
-- Right (Stack [VDouble 6.0])

-- >>> go $ EComp (EPrim (ELit 0.0)) (EComp (EPrim (EVec [1.0,2.0,3.0])) (EPrim1 EFold (EPrim EAdd)))
-- Right (Stack [VDouble 6.0])

-- >>> go $ EComp (EPrim (EVec [1.0,2.0,3.0])) (EKappa (EVar 102) (EComp (EPrim (ELit 0.0)) (EComp (EPrim (ELit 0.0)) (EComp (ERef (EVar 102)) (EPrim1 EFold (EKappa (EVar 103) (EKappa (EVar 104) (EKappa (EVar 105) (EComp (ERef (EVar 103)) (EComp (ERef (EVar 105)) (EComp (EPrim EAdd) (EComp (EPrim (ELit 1.0)) (EComp (ERef (EVar 104)) (EPrim EAdd))))))))))))))
-- Right (Stack [VDouble 3.0,VDouble 6.0])

-- >>> go $ EComp (EPrim (EVec [100, 200, 135])) (EKappa (EVar 104) (EComp (EPrim (ELit 0.0)) (EComp (EPrim (ELit 0.0)) (EComp (ERef (EVar 104)) (EComp (EPrim1 EFold (EKappa (EVar 105) (EKappa (EVar 106) (EKappa (EVar 107) (EComp (ERef (EVar 105)) (EComp (ERef (EVar 107)) (EComp (EPrim EAdd) (EComp (EPrim (ELit 1.0)) (EComp (ERef (EVar 106)) (EPrim EAdd)))))))))) (EComp (EKappa (EVar 102) (EKappa (EVar 103) (EComp (ERef (EVar 102)) (ERef (EVar 103))))) (EPrim EDiv)))))))
-- Right (Stack [VDouble 145.0])

-- >>> go $ EComp (EPrim (EVec [100, 200, 135])) (EKappa (EVar 102) (EComp (EPrim (ELit 0.0)) (EComp (EPrim (ELit 0.0)) (EComp (ERef (EVar 102)) (EComp (EPrim1 EFold (EKappa (EVar 103) (EKappa (EVar 104) (EKappa (EVar 105) (EComp (EPrim (ELit 1.0)) (EComp (ERef (EVar 105)) (EComp (EPrim EAdd) (EComp (ERef (EVar 103)) (EComp (ERef (EVar 104)) (EPrim EAdd)))))))))) (EPrim EDiv))))))
-- Right (Stack [VDouble 145.0])

-- >>> go $ EComp (EPrim (EVec [100, 200, 135])) (EKappa (EVar 104) (EComp (ERef (EVar 104)) (EComp (EKappa (EVar 100) (EComp (EPrim (ELit 0.0)) (EComp (ERef (EVar 100)) (EPrim1 EFold (EKappa (EVar 101) (EKappa (EVar 102) (EComp (EPrim (ELit 1.0)) (EComp (ERef (EVar 102)) (EPrim EAdd))))))))) (EComp (ERef (EVar 104)) (EComp (EKappa (EVar 103) (EComp (EPrim (ELit 0.0)) (EComp (ERef (EVar 103)) (EPrim1 EFold (EPrim EAdd))))) (EPrim EDiv))))))
-- Right (Stack [VDouble 145.0])

