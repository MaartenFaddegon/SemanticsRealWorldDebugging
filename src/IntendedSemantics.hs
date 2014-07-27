module IntendedSemantics where

import Control.Monad.State(State,gets)
import Prelude hiding (Right)
import Data.Graph.Libgraph(Graph,display,showWith,findFaulty)
import Context
import Debug

-- import qualified Debug.Trace as Debug

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

reduce :: ReduceRule Expr Judgement 

reduce (Const v) = 
  return (Expression (Const v))

reduce (Lambda x e) = 
  return (Expression $ Lambda x e)

reduce (Let (x,e1) e2) = do
  stk <- gets stack
  insertHeap x (stk,e1)
  result <- reduce e2
  deleteHeap x
  return result

reduce (Apply f x) = do
  e <- eval reduce f
  case e of 
    Expression (Lambda y e) -> eval reduce (subst y x e)
    Exception msg           -> return (Exception msg)
    _                       -> return (Exception "Apply non-Lambda?")

reduce (Var x) = do
  r <- lookupHeap x
  case r of
    (stk,Exception msg) -> do
      setStack stk
      return (Exception msg)
    (stk,Expression (Const v)) -> do
      setStack stk
      return (Expression (Const v))
    (stk,Expression (Lambda y e)) -> do
      doCall stk
      return (Expression (Lambda y e))
    (stk,Expression e) -> do
      deleteHeap x
      setStack stk
      v' <- eval reduce e
      case v' of
        Exception msg -> return (Exception msg)
        Expression v  -> do
          stkv <- gets stack
          insertHeap x (stkv,v)
          setStack stk
          eval reduce (Var x)

reduce (ACCCorrect l e) = do
  stk <- gets stack
  doPush l
  eval reduce (Observed l stk Root e)

reduce (ACCFaulty l e) = do
  stk <- gets stack
  doPush l
  uid <- getUniq
  trace (Record l stk uid Root Wrong)
  r <- eval reduce e
  case r of
    (Expression (Const jmt)) -> return (Expression (Const Wrong))
    _                        -> return r


reduce (Observed l s p e) = do
  stk <- gets stack
  e' <- eval reduce e
  case e' of
    Exception msg ->
      return (Exception msg)
    Expression (Const v) -> do
      uid <- getUniq
      trace (Record l s uid p v)
      return e'
    Expression (Lambda x e) -> do
      uid <- getUniq
      let x' = "_1" ++ x; x'' = "_2" ++ x
          body = Let (x',Observed l stk (ArgOf uid) (Var x'')) 
                     (Apply (Lambda x (Observed l s (ResOf uid) e)) x')
      trace (Record l s uid p Right)
      return (Expression (Lambda x'' body))
    Expression e -> 
      return (Exception $ "Observe undefined: " ++ show e)

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

e4 = ACCCorrect "root" (Apply (ACCCorrect "N" (Let ("z",Let ("y",Var "y") (ACCCorrect "C" (Lambda "z" (ACCFaulty "N" (Const Right))))) (ACCCorrect "F" (ACCFaulty "V" (ACCCorrect "V" (Var "z")))))) "z")

e5 = ACCCorrect "root" (ACCCorrect "root" (Apply (ACCCorrect "G" (Lambda "x" (ACCCorrect "U" (Let ("y",Lambda "x" (ACCFaulty "Y" (ACCFaulty "B" (ACCCorrect "Y" (Apply (ACCFaulty "D" (Lambda "z" (Apply (Lambda "y" (Const Right)) "x"))) "y"))))) (ACCFaulty "I" (Apply (Let ("z",Apply (Lambda "y" (Apply (Const Right) "x")) "x") (ACCFaulty "V" (ACCCorrect "D" (Var "x")))) "y")))))) "y"))

e6 = ACCCorrect "root" (ACCFaulty "I" (ACCFaulty "W" (Let ("y",Var "x") (Apply (ACCFaulty "V" (Apply (Apply (Let ("x",ACCFaulty "L" (Let ("z",ACCFaulty "K" (Lambda "y" (Const Right))) (Lambda "y" (ACCFaulty "D" (Let ("x",ACCFaulty "W" (ACCCorrect "C" (Const Right))) (ACCCorrect "H" (ACCFaulty "M" (Var "y")))))))) (ACCCorrect "K" (Lambda "z" (Lambda "y" (Var "y"))))) "z") "x")) "x"))))


e6' = ACCCorrect "root" 
      ( (Let ("y",Var "x") 
          (Apply 
            (Apply
              (Apply 
                (Let 
                  ("x",ACCFaulty "L" (Lambda "y" (ACCFaulty "C" (Const Right)))) 
                  (ACCCorrect "Z" (Lambda "z" (Lambda "y" (Var "y"))))
                ) "z"
              ) "x"
            ) "x"
           )
         )
      )

-- Demonstrates that it is important to consider 'call' as well when
-- adding dependencies based on the cost centre stack.
e7 = 
  ACCCorrect "root"
  (Let 
    ("f",ACCCorrect "F1" (Lambda "x" (ACCFaulty "F2" (Const Right))))
    (Apply 
      (ACCCorrect "IN" (Lambda "y" (Apply (Var "y") "z")))
    "f"
    )
  )

-- Behaves weird: their are two records that claim to are the arg-value of the
-- same parent-record!
e8 = Apply (Lambda "x" (Let ("z",Const Right) (Apply (Let ("y",Apply (Lambda "y" (ACCCorrect "D" (Lambda "z" (ACCFaulty "G" (Var "y"))))) "z") (Apply (Var "y") "y")) "x"))) "z"
