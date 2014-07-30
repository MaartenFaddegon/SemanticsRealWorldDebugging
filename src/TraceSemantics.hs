module TraceSemantics where

import Control.Monad.State(gets)
import Prelude hiding (Right)
import Data.Graph.Libgraph(Graph,display,showWith)
import Context
import Debug

--------------------------------------------------------------------------------
-- Trace post processing

mkEquations :: (Trace String, e) -> (Trace String, e)
mkEquations (trc,reduct) = (filter isRoot . map (successors trc merge) $ trc,reduct)
  where isRoot = (== Root) . recordParent


merge rec arg res =
  if lam && top
    then rec {recordRepr = recordLabel rec ++ " " ++ val arg ++ " = " ++ val res }
  else if lam
    then rec {recordRepr = "(\\" ++ val arg ++ " -> " ++ val res ++ ")"}
  else if top
    then rec {recordRepr = recordLabel rec ++ " = " ++ recordRepr rec}
    else rec
  where lam = recordRepr rec == "\\"
        top = recordParent rec == Root
        val Nothing = "_"
        val (Just r) = recordRepr r

--------------------------------------------------------------------------------
-- Expressions

data Expr = Const    Int
          | Lambda   Name Expr
          | Apply    Expr Name
          | Var      Name
          | Let      (Name,Expr) Expr
          | ACC      Label Expr
          | Observed Label Stack Parent Expr
          deriving (Show,Eq)

--------------------------------------------------------------------------------
-- Reduction rules

reduce :: ReduceRule Expr String 

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

reduce (ACC l e) = do
  stk <- gets cxtStack
  doPush l
  eval reduce (Observed l stk Root e)

reduce (Observed l s p e) = do
  stk <- gets cxtStack
  e' <- eval reduce e
  case e' of
    Exception msg ->
      return (Exception msg)
    Expression (Const v) -> do
      uid <- getUniq
      trace (Record l s uid p (show v))
      return e'
    Expression (Lambda x e) -> do
      uid <- getUniq
      let x' = "_1" ++ x; x'' = "_2" ++ x
          body = Let (x',Observed l stk (ArgOf uid) (Var x'')) 
                     (Apply (Lambda x (Observed l s (ResOf uid) e)) x')
      trace (Record l s uid p "\\")
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
subst n m (ACC l e)          = ACC l (subst n m e)
subst n m (Observed l s p e) = Observed l s p (subst n m e)

sub :: Name -> Name -> Name -> Name
sub n m n' = if n == n' then m else n'

--------------------------------------------------------------------------------
-- Examples.

type CompGraph = Graph (Vertex String)

tracedEval :: Expr -> (ExprExc Expr,CompGraph)
tracedEval = mkGraph . mkEquations . toTuple . (evalWith' reduce)
  where toTuple (x,y,_) = (x,y)

disp :: Expr -> IO ()
disp expr = do 
  putStr messages
  (display shw) . snd . mkGraph . mkEquations $ (reduct,trc)
  where (reduct,trc,messages) = evalWith' reduce expr
        shw :: CompGraph -> String
        shw g = showWith g showVertex showArc
        showVertex = (foldl (++) "") . (map showRecord)
        showRecord = recordRepr
        showArc _  = ""

e1 = ACC "A" (Const 42)

e2 = Let ("x", Const 42) (ACC "X" (Var "x"))

e3 = Let ("i", (Const 42)) 
         (Apply (ACC "lam" (Lambda "x" (Var "x"))) "i")

e4 = Let ("i", (Const 42)) 
         (Apply (ACC "lam" (Lambda "x" (Const 1))) "i")

e5 =  ACC "main"
      ( Let ("i", (Const 42)) 
            ( Let ("id",ACC "id" (Lambda "y" (Var "y")))
                  ( Apply 
                    ( Apply 
                      ( ACC "h" 
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
  ACC "root"
  (Let 
    ("f",ACC "F1" (Lambda "x" (ACC "F2" (Const 1))))
    (Apply 
      (ACC "IN" (Lambda "y" (Apply (Var "y") "z")))
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
          ("z",Const 42) 
          (Apply 
            (Let 
              ("y",Apply (Lambda "y" (ACC"D" (Lambda "z" (ACC"G" (Var "y"))))) "z")
              (Apply (Var "y") "y")
            )
            "x"
          )
        )
      ) "z"  -- Try replacing "z" with "a" here
