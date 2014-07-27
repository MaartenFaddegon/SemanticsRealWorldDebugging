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
    then rec {recordValue = recordLabel rec ++ " " ++ val arg ++ " = " ++ val res }
  else if lam
    then rec {recordValue = "(\\" ++ val arg ++ " -> " ++ val res ++ ")"}
  else if top
    then rec {recordValue = recordLabel rec ++ " = " ++ recordValue rec}
    else rec
  where lam = recordValue rec == "\\"
        top = recordParent rec == Root
        val Nothing = "_"
        val (Just r) = recordValue r

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

reduce :: ReduceRule String Expr

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
          setStack stk
          eval reduce trcv (Var x)

reduce trc (ACC l e) = do
  stk <- gets stack
  doPush l
  eval reduce trc (Observed l stk Root e)

reduce trc (Observed l s p e) = do
  stk <- gets stack
  (trc',e') <- eval reduce trc e
  case e' of
    Exception msg ->
      return (trc',Exception msg)
    Expression (Const v) -> do
      uid <- getUniq
      return (trace (Record l s uid p (show v)) trc',e')
    Expression (Lambda x e) -> do
      uid <- getUniq
      let x' = "_1" ++ x; x'' = "_2" ++ x
          body = Let (x',Observed l stk (ArgOf uid) (Var x'')) 
                     (Apply (Lambda x (Observed l s (ResOf uid) e)) x')
          trc'' = trace (Record l s uid p "\\") trc'
      return (trc'',Expression (Lambda x'' body))
    Expression e -> 
      return (trc,Exception $ "Observe undefined: " ++ show e)

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

disp :: Expr -> IO ()
disp expr = do 
  putStr messages
  (display shw) . snd . mkGraph . mkEquations $ (reduct,trc)
  where (reduct,trc,messages) = evalWith' reduce expr
        shw :: CompGraph -> String
        shw g = showWith g showVertex showArc
        showVertex = (foldl (++) "") . (map showRecord)
        showRecord = recordValue
        showArc _  = ""

-- run' = evalWith' reduce

e1 = ACC "A" (Const 42)

e2 = Let ("x", Const 42) (ACC "X" (Var "x"))

e3 = Let ("i", (Const 42)) 
         (Apply (Lambda "x" (Var "x")) "i")

e4 = Let ("i", (Const 42)) 
         (Apply (ACC "lam" (Lambda "x" (Var "x"))) "i")

e5 = Let ("i", (Const 42)) 
         (Apply (ACC "lam" (Lambda "x" (Const 1))) "i")

e6 =  ACC "main"
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


-- Behaves weird: their are two records that claim to are the arg-value of the
-- same parent-record!
e8 = Apply (Lambda "x" (Let ("z",Const 42) (Apply (Let ("y",Apply (Lambda "y" (ACC"D" (Lambda "z" (ACC"G" (Var "y"))))) "z") (Apply (Var "y") "y")) "x"))) "z"
