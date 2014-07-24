module IntendedSemantics where

import Control.Monad.State(State,gets)
import Prelude hiding (Right)
import Data.Graph.Libgraph(Graph,display,showWith,findFaulty)
import Context
import Debug

--------------------------------------------------------------------------------
-- Tracing

data Judgement  = Right | Wrong       deriving (Show,Eq,Ord)

--------------------------------------------------------------------------------
-- Trace post processing

-- To render graphs
mkEquations' :: (Trace Judgement, e) -> (Trace String, e)
mkEquations' (trc,reduct) = (map toString trc, reduct)
  where toString rec = rec {recordValue = (recordLabel rec) ++ " = " 
                                        ++ (show $ recordValue rec)}

-- To quickcheck
mkEquations :: (Trace Judgement, e) -> (Trace Judgement, e)
mkEquations (trc,reduct) = (filter isRoot . map (successors trc merge) $ trc,reduct)
  where isRoot = (== Root) . recordParent

merge :: Record Judgement -> Maybe (Record Judgement) -> Maybe (Record Judgement)
      -> Record Judgement
merge rec arg res = rec{recordValue=(recordValue rec) `or` (jmt arg) `or` (jmt res)}
  where jmt mr = case mr of Just r -> recordValue r; Nothing -> Right
        or Wrong _ = Wrong
        or _ Wrong = Wrong
        or _ _     = Right
          
--------------------------------------------------------------------------------
-- Expressions

data Expr = Const    Judgement
          | Lambda   Name Expr
          | Apply    Expr Name
          | Var      Name
          | Let      (Name,Expr) Expr
          | ACCCorrect Label Expr
          | ACCFaulty  Label Expr
          | Observed   Label Stack Parent Expr
          deriving (Show,Eq)

--------------------------------------------------------------------------------
-- Reduction rules.

reduce :: ReduceRule Judgement Expr

reduce trc (Const v) = 
  return (trc,Expression (Const v))

reduce trc (Lambda x e) = 
  return (trc,Expression $ Lambda x e)

reduce trc (Let (x,e1) e2) = do
  stk <- gets stack
  insertHeap x (stk,e1)
  reduce trc e2

reduce trc (Apply f x) = do
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
    (stk,Expression (Const v)) -> do
      setStack stk
      return (trc,Expression (Const v))
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
          -- MF TODO: Need to check this (here and for TraceSemantics). I think
          -- that Simon Marlow reverts back to stk here. But that certainly
          -- leads to weird stacks. Try e3 for example.
          -- setStack stk
          eval reduce trcv (Var x)

reduce trc (ACCCorrect l e) = do
  stk <- gets stack
  doPush l
  eval reduce trc (Observed l stk Root e)

reduce trc (ACCFaulty l e) = do
  stk <- gets stack
  doPush l
  uid <- getUniq
  r <- eval reduce (trace (Record l stk uid Root Wrong) trc) e
  case r of
    (trc,Expression (Const jmt)) -> return (trc,Expression (Const Wrong))
    _                            -> return r


reduce trc (Observed l s p e) = do
  stk <- gets stack
  (trc',e') <- eval reduce trc e
  case e' of
    Exception msg ->
      return (trc',Exception msg)
    Expression (Const v) -> do
      uid <- getUniq
      return (trace (Record l s uid p v) trc',e')
    Expression (Lambda x e) -> do
      uid <- getUniq
      let x' = "_" ++ x; x'' = "__" ++ x
          body = Let (x',Observed l stk (ArgOf uid) (Var x'')) 
                     (Apply (Lambda x (Observed l s (ResOf uid) e)) x')
          trc'' = trace (Record l s uid p Right) trc'
      return (trc'',Expression (Lambda x'' body))
    Expression e -> 
      return (trc,Exception $ "Observe undefined: " ++ show e)

--------------------------------------------------------------------------------
-- Substituting variable names.

subst :: Name -> Name -> Expr -> Expr
subst n m (Const v)        = Const v
subst n m (Lambda n' e)      = Lambda (sub n m n') (subst n m e)
subst n m (Apply e n')       = Apply (subst n m e) (sub n m n')
subst n m (Var n')           = Var (sub n m n')
subst n m (Let (n',e1) e2)   = Let ((sub n m n'),(subst n m e1)) (subst n m e2)
subst n m (ACCCorrect l e)   = ACCCorrect l (subst n m e)
subst n m (ACCFaulty l e)    = ACCFaulty l (subst n m e)
subst n m (Observed l s p e) = Observed l s p (subst n m e)

sub :: Name -> Name -> Name -> Name
sub n m n' = if n == n' then m else n'

--------------------------------------------------------------------------------
-- Examples.

type CompGraph = Graph (Vertex String)

findFaulty' :: Graph (Vertex Judgement) -> [Vertex Judgement]
findFaulty' = findFaulty wrongCC mergeCC
  where mergeCC ws = foldl (++) [] ws
        wrongCC = foldl (\w r -> case recordValue r of Wrong -> True; _ -> w) False

debug :: Expr -> IO ()
debug redex = do
  let (reduct,compgraph) = mkGraph . mkEquations . (evalWith reduce) $ redex
  print (findFaulty' compgraph)

tracedEval :: Expr -> (ExprExc Expr,CompGraph)
tracedEval = mkGraph . mkEquations' . mkEquations . (evalWith reduce)

disp :: Expr -> IO ()
disp redex = do
  let (reduct,compgraph) = tracedEval redex
  print reduct
  (display shw) compgraph

  where shw :: CompGraph -> String
        shw g = showWith g showVertex showArc
        showVertex = (foldl (++) "") . (map showRecord)
        -- showRecord = thd
        showRecord rec = (recordValue rec) ++ " (with stack "
                        ++ show (recordStack rec) ++ ")\n"
        showArc _  = ""

e1 = ACCFaulty "Z" (ACCFaulty "U" (ACCCorrect "Z" (ACCCorrect "N" (Const Right))))

e2 = Let ("x",ACCCorrect "letx" (Const Right)) (ACCFaulty "in" (Var "x"))
e2' = ACCFaulty "root" (Let ("x",ACCCorrect "letx" (Const Right)) (ACCFaulty "in" (Var "x")))

e3 = ACCCorrect "A" (ACCCorrect "B"((Let ("z",ACCCorrect "C" (Lambda "y" (ACCCorrect "lam" (Const Right)))) (Let ("x",Let ("y",Apply (Const Right) "x") (ACCFaulty "X" (Let ("x",(Const Right)) (Const Right)))) (Apply (Var "z") "z")))))


e3' = Let ("z",ACCCorrect "C" (Lambda "y" (ACCCorrect "lam" (Const Right)))) 
          (Apply (Var "z") "z")

e4 = Apply (ACCCorrect "N" (Let ("z",Let ("y",Var "y") (ACCCorrect "C" (Lambda "z" (ACCFaulty "N" (Const Right))))) (ACCCorrect "F" (ACCFaulty "V" (ACCCorrect "V" (Var "z")))))) "z"
