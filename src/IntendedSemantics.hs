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
  where toString rec = rec {recordRepr = (recordLabel rec) ++ " = " 
                                        ++ (show $ recordRepr rec)}

-- To quickcheck
mkEquations :: (Trace Judgement, e) -> (Trace Judgement, e)
mkEquations (trc,reduct) = (filter isRoot . map (successors trc merge) $ trc,reduct)
  where isRoot = (== Root) . recordParent

merge :: Record Judgement -> Maybe (Record Judgement) -> Maybe (Record Judgement)
      -> Record Judgement
merge rec arg res = rec{recordRepr=(recordRepr rec) `or` (jmt arg) `or` (jmt res)}
  where jmt mr = case mr of Just r -> recordRepr r; Nothing -> Right
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
  stk <- gets cxtStack
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
          stkv <- gets cxtStack
          insertHeap x (stkv,v)
          setStack stk
          eval reduce (Var x)

reduce (ACCCorrect l e) = do
  stk <- gets cxtStack
  doPush l
  eval reduce (Observed l stk Root e)

reduce (ACCFaulty l e) = do
  stk <- gets cxtStack
  doPush l
  uid <- getUniq
  trace (Record l stk uid Root Wrong)
  r <- eval reduce e
  case r of
    (Expression (Const jmt)) -> return (Expression (Const Wrong))
    _                        -> return r


reduce (Observed l s p e) = do
  stk <- gets cxtStack
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
subst n m (Const v)          = Const v
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

findFaulty' :: Graph (Vertex Judgement) -> [Vertex Judgement]
findFaulty' = findFaulty wrongCC mergeCC
  where mergeCC ws = foldl (++) [] ws
        wrongCC = foldl (\w r -> case recordRepr r of Wrong -> True; _ -> w) False

debug :: Expr -> IO ()
debug redex = do
  let (reduct,compgraph) = mkGraph . mkEquations . (evalWith reduce) $ redex
  print (findFaulty' compgraph)

tracedEval :: Expr -> (ExprExc Expr,Graph (Vertex String))
tracedEval = mkGraph . mkEquations' . mkEquations . (evalWith reduce)

disp :: Expr -> IO ()
disp redex = do
  let (reduct,compgraph) = tracedEval redex
  print reduct
  (display shw) compgraph

  where shw :: (Graph (Vertex String)) -> String
        shw g = showWith g showVertex showArc
        showVertex = (foldl (++) "") . (map showRecord)
        showRecord rec = (recordRepr rec) ++ " (with stack "
                        ++ show (recordStack rec) ++ ")\n"
        showArc _  = ""

e1 = ACCFaulty "A" (Const Right)

e2 = Let ("x", Const Right) (ACCFaulty "X" (Var "x"))

e3 = Let ("i", (Const Right)) 
         (Apply (ACCFaulty "lam" (Lambda "x" (Var "x"))) "i")

e4 = Let ("i", (Const Right)) 
         (Apply (ACCFaulty "lam" (Lambda "x" (Const Right))) "i")

e5 =  ACCCorrect "main"
      ( Let ("i", (Const Right)) 
            ( Let ("id",ACCFaulty "id" (Lambda "y" (Var "y")))
                  ( Apply 
                    ( Apply 
                      ( ACCCorrect "h" 
                        ( Lambda "f" 
                          ( Lambda "x"
                            ( Apply (Var "f") "x"
                            )
                          )
                        )
                      ) "id"
                    ) "i"
                  )
            )
      )

-- Demonstrates that it is important to consider 'call' as well when
-- adding dependencies based on the cost centre stack.
e6 = 
  ACCCorrect "root"
  (Let 
    ("f",ACCCorrect "F1" (Lambda "x" (ACCFaulty "F2" (Const Right))))
    (Apply 
      (ACCCorrect "IN" (Lambda "y" (Apply (Var "y") "z")))
    "f"
    )
  )

-- A demonstration of 'strange behaviour' because we don't properly
-- freshen our varibles: scopes don't work as we would expect them to.
-- In this case it results in two records that claim to are the arg-value of
-- the same parent-record.
e7 = Apply
      (Lambda "x"
        (Let
          ("z",Const Right)
          (Apply
            (Let
              ("y",Apply (Lambda "y" (ACCCorrect "D" (Lambda "z" (ACCFaulty "G" (Var "y"))))) "z")
              (Apply (Var "y") "y")
            )
            "x"
          )
        )
      ) "z"  -- Try replacing "z" with "a" here
