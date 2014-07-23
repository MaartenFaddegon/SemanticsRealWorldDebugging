module IntendedSemantics where

import Control.Monad.State(State,gets)
import Prelude hiding (Right)
import Data.Graph.Libgraph(Graph,display,showWith)
import Context
import Debug

--------------------------------------------------------------------------------
-- Tracing.

data Judgement  = Right | Wrong       deriving (Show,Eq,Ord)

--------------------------------------------------------------------------------
-- Trace post processing (only for displaying, not used for QuickChecking)

mkEquations :: (Trace Judgement, e) -> (Trace String, e)
mkEquations (trc,reduct) = (map toString trc, reduct)
  where toString (lbl,stk,jmt) = (lbl,stk,lbl ++ " = " ++ show jmt)

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

reduce :: ReduceRule Judgement Expr

reduce trc Const = 
  return (trc,Expression Const)

reduce trc (Lambda x e) = 
  return (trc,Expression $ Lambda x e)

reduce trc (ACCCorrect l e) = do
  stk <- gets stack
  doPush l
  eval reduce trc (Observed l stk e)

reduce trc (ACCFaulty l e) = do
  stk <- gets stack
  doPush l
  eval reduce (trace (l,stk,Wrong) trc) e

reduce trc (Let (x,e1) e2) = do
  stk <- gets stack
  insertHeap x (stk,e1)
  eval reduce trc e2

reduce trc orig@(Apply f x) = do
  (trc_lam, e) <- eval reduce trc f
  case e of 
    Expression (Lambda y e) -> eval reduce trc_lam (subst y x e)
    Exception msg           -> return (trc_lam,Exception msg)
    _                       -> return (trc_lam,Exception "Apply non-Lambda?")

reduce trc (Var x) = do
  r <- lookupHeap x
  case r of
    (stk,Exception msg) -> do
      setStack stk
      return (trc,Exception msg)
    (stk,Expression Const) -> do
      setStack stk
      return (trc,Expression Const)
    (stk,Expression (Lambda y e)) -> do
      doCall stk
      return (trc,Expression (Lambda y e))
    (stk,Expression e) -> do
      deleteHeap x
      setStack stk
      (trcv,v') <- eval reduce trc e
      case v' of
        Exception msg -> return (trcv,Exception msg)
        Expression v  -> do
          stkv <- gets stack
          insertHeap x (stkv,v)
          eval reduce trcv (Var x)

-- MF TODO: similar changes to that of the TraceSemantics Observe rule need to
-- be made here.
reduce trc (Observed l s e) = do
  case e of Const              -> return (trace (l,s,Right) trc,Expression Const)
            (ACCFaulty l' e')  -> eval reduce (trace (l,s,Wrong) trc) (ACCFaulty l' e')
            (ACCCorrect l' e') -> eval reduce trc (ACCCorrect l' (Observed l s e'))
            (Let (x,e1) e2)    -> eval reduce trc (Let (x,e1) (Observed l s e2))
            _ -> do
              (trc',e') <- eval reduce trc e
              case e' of
                Exception msg  -> return (trc',Exception msg)
                Expression e'' -> eval reduce trc' (Observed l s e'')

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

--------------------------------------------------------------------------------
-- Examples.

type CompGraph = Graph (Vertex String)

tracedEval :: Expr -> (ExprExc Expr,CompGraph)
tracedEval = mkGraph . mkEquations . (evalWith reduce)

disp :: Expr -> IO ()
disp redex = do
  let (reduct,compgraph) = tracedEval redex
  (display shw) compgraph
  print reduct

  where shw :: CompGraph -> String
        shw g = showWith g showVertex showArc
        showVertex = (foldl (++) "") . (map showRecord)
        -- showRecord = thd
        showRecord (lbl,stk,str) = str ++ " (with stack " ++ show stk ++ ")\n"
        showArc _  = ""

e1 = ACCFaulty "Z" (ACCFaulty "U" (ACCCorrect "Z" (ACCCorrect "N" Const)))

e2 = Let ("x",ACCCorrect "letx" Const) (ACCFaulty "in" (Var "x"))
