module TraceSemantics where

import Control.Monad.State(State)
import Prelude hiding (Right)
import Context


--------------------------------------------------------------------------------
-- Tracing.

data Id = Root | Id Int
  deriving (Show,Eq)

data Value  = Value { traceId :: Id, traceParent :: Id, traceValue :: String }
  deriving (Show)

type Record = (Label,Stack,Value)

trace :: Record -> Trace Record -> Trace Record
trace = (:)

--------------------------------------------------------------------------------
-- Expressions.

data Expr = Const    Int
          | Lambda   Name Expr
          | Apply    Expr Name
          | Var      Name
          | Let      (Name,Expr) Expr
          | ACC      Label Expr
          | Observed Label Stack Id Expr
          deriving (Show,Eq)

--------------------------------------------------------------------------------
-- The reduction rules.

reduce :: Stack -> Trace Record -> Expr -> State (Context Expr) (Stack,Trace Record,ExprExc Expr)

reduce stk trc (Const i) = 
  return (stk,trc,Expression (Const i))

reduce stk trc (Lambda x e) = 
  return (stk,trc,Expression $ Lambda x e)

reduce stk trc (ACC l e) =
  evalUpto reduce (push l stk) trc (Observed l stk Root e)

reduce stk trc (Let (x,e1) e2) = do
  insertHeap x (stk,e1)
  reduce stk trc e2

reduce stk trc orig@(Apply f x) = do
  (stk_lam, trc_lam, e) <- evalUpto reduce stk trc f
  case e of 
    Expression (Lambda y e) -> evalUpto reduce stk_lam trc_lam (subst y x e)
    Exception msg           -> return (stk_lam,trc_lam,Exception msg)
    _                       -> return (stk_lam,trc_lam,Exception "Apply non-Lambda?")

reduce stk trc (Var x) = do
  r <- lookupHeap x
  case r of
    (stk',Exception msg)           -> return (stk',trc,Exception msg)
    (stk',Expression (Const i))    -> return (stk',trc,Expression (Const i))
    (stk',Expression (Lambda y e)) -> return (call stk stk',trc,Expression (Lambda y e))
    (stk',Expression e) -> do
      deleteHeap x
      (stkv,trcv,v') <- evalUpto reduce stk' trc e
      case v' of
        Exception msg -> return (stkv,trcv,Exception msg)
        Expression v  -> do
          insertHeap x (stkv,v)
          evalUpto reduce stk trcv (Var x) -- Notice how we retain the trace but swap back the stack

-- MF TODO: Ik denk dat alle gevallen hier behandeld moeten worden ipv de _ op het eind?
reduce stk trc (Observed l s p e) = do
  (stk',trc',e') <- evalUpto reduce stk trc e
  case e' of
    Exception msg           -> return (stk',trc',Exception msg)
    Expression (Const i)    -> do
      id <- getUniq
      return (stk',trace (l,s,Value (Id id) p (show i)) trc',Expression (Const i))
    Expression (Lambda x e) -> do
      id <- getUniq
      let x' = "_" ++ x; x'' = "__" ++ x
          lRes = l ++ "-result"; lArg = l ++ "-argument"
          innerLam = Lambda x (Observed lRes s (Id id) e)
          body     = Let (x',Observed lArg stk (Id id) (Var x'')) 
                         (Apply innerLam x')
          trc''     = trace (l,s,Value (Id id) p "\\") trc'
      evalUpto reduce stk' trc'' (Lambda x'' body)

--------------------------------------------------------------------------------
-- Substituting variable names.

subst :: Name -> Name -> Expr -> Expr
subst n m (Const i)          = Const i
subst n m (Lambda n' e)      = Lambda (sub n m n') (subst n m e)
subst n m (Apply e n')       = Apply (subst n m e) (sub n m n')
subst n m (Var n')           = Var (sub n m n')
subst n m (Let (n',e1) e2)   = Let ((sub n m n'),(subst n m e1)) (subst n m e2)
subst n m (ACC l e)          = ACC l (subst n m e)
subst n m (Observed l s p e) = Observed l s p (subst n m e)

sub :: Name -> Name -> Name -> Name
sub n m n' = if n == n' then m else n'


--------------------------------------------------------------------------------
-- Examples.

eval   = evalE reduce
eval' = evalE' reduce

e1 = ACC "A" (Const 42)

e2 = Let ("x", Const 42) (ACC "X" (Var "x"))

e3 = Let ("i", (Const 42)) 
         (Apply (Lambda "x" (Var "x")) "i")

e4 = Let ("i", (Const 42)) 
         (Apply (ACC "lam" (Lambda "x" (Var "x"))) "i")

e5 = Let ("i", (Const 42)) 
         (Apply (ACC "lam" (Lambda "x" (Const 1))) "i")
