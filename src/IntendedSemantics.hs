module IntendedSemantics where

import Control.Monad.State(State,gets)
import Prelude hiding (Right)
import Data.Graph.Libgraph(Graph,display,showWith,findFaulty)
import Context
import Debug
import qualified Debug.Trace as Debug

--------------------------------------------------------------------------------
-- Tracing.

data Judgement  = Right | Wrong       deriving (Show,Eq,Ord)

data Value  = Value { traceId :: Id, traceParent :: Parent, traceValue :: Judgement }
  deriving (Show)

--------------------------------------------------------------------------------
-- Trace post processing (only for displaying, not used for QuickChecking)

mkEquations' :: (Trace Judgement, e) -> (Trace String, e)
mkEquations' (trc,reduct) = (map toString trc, reduct)
  where toString (lbl,stk,jmt) = (lbl,stk,lbl ++ " = " ++ show jmt)

mkEquations :: (Trace Value, e) -> (Trace Judgement, e)
mkEquations (trc,reduct) = (map toJudgement . filter isRoot . map (replace trc) $ trc,reduct)
  where isRoot (_,_,val)          = traceParent val == Root
        toJudgement (lbl,stk,val) = (lbl,stk,traceValue val)

replace :: Trace Value -> Record Value -> Record Value
replace trc (lbl,stk,val)
  = (lbl,stk,val{traceValue = jmt})
    where jms = map (traceValue . thd) (children trc (traceId val))
          jmt = foldl or (traceValue val) jms
          or Wrong _ = Wrong
          or _ Wrong = Wrong
          or _ _     = Right
          

-- MF TODO: need to collect children of children as well
children :: Trace Value -> Id -> [Record Value]
children trc unq = filter (\(_,_,val) -> chd $ traceParent val) trc
  where chd (ArgOf unq') = unq' == unq
        chd (ResOf unq') = unq' == unq
        chd _            = False

--------------------------------------------------------------------------------
-- Expressions.

data Expr = Const  Judgement
          | Lambda Name Expr
          | Apply  Expr Name
          | Var    Name
          | Let    (Name,Expr) Expr
          | ACCCorrect Label Expr
          | ACCFaulty  Label Expr
          | Observed   Label Stack Parent Expr
          deriving (Show,Eq)

--------------------------------------------------------------------------------
-- The reduction rules.

reduce :: ReduceRule Value Expr

reduce trc (Const jmt) = 
  return (trc,Expression (Const jmt))

reduce trc (Lambda x e) = 
  return (trc,Expression $ Lambda x e)

reduce trc (ACCCorrect l e) = do
  stk <- gets stack
  doPush l
  eval reduce trc (Observed l stk Root e)

reduce trc (ACCFaulty l e) = do
  stk <- gets stack
  doPush l
  id <- getUniq
  r <- eval reduce (trace (l,stk,Value id Root Wrong) trc) e
  case r of
    (trc,Expression (Const jmt)) -> return (trc,Expression (Const Wrong))
    _                            -> return r

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
    (stk,Expression (Const jmt)) -> do
      setStack stk
      return (trc,Expression (Const jmt))
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
          setStack stk
          eval reduce trcv (Var x)

-- MF TODO: similar changes to that of the TraceSemantics Observe rule need to
-- be made here.
--X reduce trc (Observed l s e) = do
--X   case e of Const              -> return (trace (l,s,Right) trc,Expression Const)
--X             (ACCFaulty l' e')  -> eval reduce (trace (l,s,Wrong) trc) (ACCFaulty l' e')
--X             (ACCCorrect l' e') -> eval reduce trc (ACCCorrect l' (Observed l s e'))
--X             (Let (x,e1) e2)    -> eval reduce trc (Let (x,e1) (Observed l s e2))
--X             _ -> do
--X               (trc',e') <- eval reduce trc e
--X               case e' of
--X                 Exception msg  -> return (trc',Exception msg)
--X                 Expression e'' -> eval reduce trc' (Observed l s e'')

reduce trc (Observed l s p e) = do
  stk <- gets stack
  (trc',e') <- eval reduce trc e
  case (Debug.trace ("* Observed redex reduces to " ++ show e') e') of
    Exception msg -> 
      return (trc',Exception msg)
    Expression (Const jmt) -> do
      id <- getUniq
      return (trace (l,s,Value id p jmt) trc, e')
    Expression (Lambda x e) -> do
      id <- getUniq
      let x' = "_" ++ x; x'' = "__" ++ x
          body = Let (x',Observed l stk (ArgOf id) (Var x'')) 
                     (Apply (Lambda x (Observed l s (ResOf id) e)) x')
          trc'' = trace (l,s,Value id p Right) trc'
      return (trc'', Expression (Lambda x'' body))
    Expression e -> 
      return (trc,Exception $ "Observe undefined: " ++ show e)

--------------------------------------------------------------------------------
-- Substituting variable names.

subst :: Name -> Name -> Expr -> Expr
subst n m (Const jmt)        = Const jmt
subst n m (Lambda n' e)      = Lambda (sub n m n') (subst n m e)
subst n m (Apply e n')       = Apply (subst n m e) (sub n m n')
subst n m (Var n')           = Var (sub n m n')
subst n m (Let (n',e1) e2)   = Let ((sub n m n'),(subst n m e1)) (subst n m e2)
subst n m (ACCCorrect l e)   = ACCCorrect l (subst n m e)
subst n m (ACCFaulty l e)    = ACCFaulty l (subst n m e)
subst n m (Observed l s p e) = (Observed l s p (subst n m e))

sub :: Name -> Name -> Name -> Name
sub n m n' = if n == n' then n' else m

--------------------------------------------------------------------------------
-- Examples.

type CompGraph = Graph (Vertex String)

findFaulty' :: Graph (Vertex Judgement) -> [Vertex Judgement]
findFaulty' = findFaulty wrongCC mergeCC
  where mergeCC ws = foldl (++) [] ws
        wrongCC = foldl (\w r -> case r of (_,_,Wrong) -> True; _ -> w) False

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
        showRecord (lbl,stk,str) = str ++ " (with stack " ++ show stk ++ ")\n"
        showArc _  = ""

e1 = ACCFaulty "Z" (ACCFaulty "U" (ACCCorrect "Z" (ACCCorrect "N" (Const Right))))

e2 = Let ("x",ACCCorrect "letx" (Const Right)) (ACCFaulty "in" (Var "x"))
e2' = ACCFaulty "root" (Let ("x",ACCCorrect "letx" (Const Right)) (ACCFaulty "in" (Var "x")))

e3 = ACCCorrect "A" (ACCCorrect "B"((Let ("z",ACCCorrect "C" (Lambda "y" (ACCCorrect "lam" (Const Right)))) (Let ("x",Let ("y",Apply (Const Right) "x") (ACCFaulty "X" (Let ("x",(Const Right)) (Const Right)))) (Apply (Var "z") "z")))))


e3' = Let ("z",ACCCorrect "C" (Lambda "y" (ACCCorrect "lam" (Const Right)))) 
          (Apply (Var "z") "z")
