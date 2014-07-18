module IntendedSemantics where

import Control.Monad.State(State)
import Prelude hiding (Right)
import Context

--------------------------------------------------------------------------------
-- Expressions.

data Expr = Const
          | Lambda Name Expr
          | Apply  Expr Name
          | Var    Name
          | Let    (Name,Expr) Expr
          | ACCCorrect Label Expr
          | ACCFaulty  Label Expr
          | Observed   Label Stack Expr
          deriving (Show,Eq)

--------------------------------------------------------------------------------
-- The reduction rules.

eval :: Stack -> Trace -> Expr -> State (Context Expr) (Stack,Trace,ExprExc Expr)

eval stk trc Const = 
  return (stk,trc,Expression Const)

eval stk trc (Lambda x e) = 
  return (stk,trc,Expression $ Lambda x e)

eval stk trc (ACCCorrect l e) =
  evalUpto eval (push l stk) trc (Observed l stk e)

eval stk trc (ACCFaulty l e)  =
  evalUpto eval (push l stk) (trace (l,stk,Wrong) trc) e

eval stk trc (Let (x,e1) e2) = do
  insertHeap x (stk,e2)
  eval stk trc e2

-- We added a special case for weird testcases that try to apply non-Lambda
-- expressions. And we break out of endless loops by returning a Const when we
-- detect such a loop.
eval stk trc orig@(Apply f x) = do
  (stk_lam, trc_lam, e) <- evalUpto eval stk trc f
  case e of 
    Expression (Lambda y e) -> evalUpto eval stk_lam trc_lam (subst y x e)
    Exception msg           -> return (stk_lam,trc_lam,Exception msg)
    _                       -> return (stk_lam,trc_lam,Exception "Apply non-Lambda?")

eval stk trc (Var x) = do
  r <- lookupHeap x
  case r of
    (stk',Exception msg)           -> return (stk',trc,Exception msg)
    (stk',Expression Const)        -> return (stk',trc,Expression Const)
    (stk',Expression (Lambda y e)) -> return (call stk stk',trc,Expression (Lambda y e))
    (stk',Expression e) -> do
      deleteHeap x
      (stkv,trcv,v') <- evalUpto eval stk' trc e
      case v' of
        Exception msg -> return (stkv,trcv,Exception msg)
        Expression v  -> do
          insertHeap x (stkv,v)
          evalUpto eval stk trcv (Var x) -- Notice how we retain the trace but swap back the stack

-- MF TODO: Ik denk dat alle gevallen hier behandeld moeten worden ipv de _ op het eind?
eval stk trc (Observed l s e) = do
  case e of Const              -> return (stk,trace (l,s,Right) trc,Expression Const)
            (ACCFaulty l' e')  -> evalUpto eval stk (trace (l,s,Wrong) trc) (ACCFaulty l' e')
            (ACCCorrect l' e') -> evalUpto eval stk trc (ACCCorrect l' (Observed l s e'))
            (Let (x,e1) e2)    -> evalUpto eval stk trc (Let (x,e1) (Observed l s e2))
            _ -> do
              (stk',trc',e') <- evalUpto eval stk trc e
              case e' of
                Exception msg  -> return (stk',trc',Exception msg)
                Expression e'' -> evalUpto eval stk' trc' (Observed l s e'')

--------------------------------------------------------------------------------
-- Substituting variable names.

subst :: Name -> Name -> Expr -> Expr
subst n m Const             = Const
subst n m (Lambda n' e)     = Lambda (sub n m n') (subst n m e)
subst n m (Apply e n')      = Apply (subst n m e) (sub n m n')
subst n m (Var n')          = Var (sub n m n')
subst n m (Let (n',e1) e2)  = Let ((sub n m n'),(subst n m e1)) (subst n m e2)
subst n m (ACCCorrect l e) = ACCCorrect l (subst n m e)
subst n m (ACCFaulty l e)  = ACCFaulty l (subst n m e)

sub :: Name -> Name -> Name -> Name
sub n m n' = if n == n' then n' else m