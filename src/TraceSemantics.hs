module TraceSemantics where

import Control.Monad.State(State,gets)
import Prelude hiding (Right)
import Context
import Debug
import Data.Graph.Libgraph(Graph,display,showWith)

--------------------------------------------------------------------------------
-- Tracing

type Id = Int

data Parent = Root | ArgOf Id | ResOf Id
  deriving (Show,Eq)

data Value  = Value { traceId :: Id, traceParent :: Parent, traceValue :: String }
  deriving (Show)

trace :: Record Value -> Trace Value -> Trace Value
trace = (:)

--------------------------------------------------------------------------------
-- Trace post processing


mkEquations (reduct,trc) = (reduct,map toString . filter isRoot . map (replace True trc) $ trc)
  where isRoot (_,_,val)   = traceParent val == Root
        toString (lbl,stk,val) = (lbl,stk,traceValue val)

 
replace top trc (lbl,stk,val) 
  = if traceValue val == "\\" && top
      then (lbl,stk,val{ traceValue = lbl ++ " " ++ arg ++ " = " ++ res })
    else if traceValue val == "\\"
      then (lbl,stk,val{ traceValue = "(\\" ++ arg ++ " -> " ++ res ++ ")"})
    else if top
      then (lbl,stk,val{ traceValue = lbl ++ " = " ++ traceValue val })
    else (lbl,stk,val)
  where (res,arg) = children trc (traceId val)

children :: Trace Value -> Id -> (String, String)
children trc id = (f (ArgOf id),f (ResOf id))
  where f p = case filter (\(_,_,val) -> traceParent val == p) trc of
                []  -> "_"
                [r] -> (traceValue . thd) (replace False trc r)

thd :: (a,b,c) -> c
thd (_,_,z) = z

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

reduce :: Trace Value -> Expr -> State (Context Expr) (Trace Value,ExprExc Expr)

reduce trc (Const i) = 
  return (trc,Expression (Const i))

reduce trc (Lambda x e) = 
  return (trc,Expression $ Lambda x e)

reduce trc (Let (x,e1) e2) = do
  stk <- gets stack
  insertHeap x (stk,e1)
  reduce trc e2

reduce trc orig@(Apply f x) = do
  (trc_lam, e) <- eval reduce trc f
  case e of 
    Expression (Lambda y e) -> eval reduce trc_lam (subst y x e)
    Exception msg           -> return (trc_lam,Exception msg)
    _                       -> return (trc_lam,Exception "Apply non-Lambda?")

reduce trc (ACC l e) = do
  stk <- gets stack
  doPush l
  eval reduce trc (Observed l stk Root e)

reduce trc (Var x) = do
  r <- lookupHeap x
  case r of
    (stk,Exception msg) -> do
      setStack stk
      return (trc,Exception msg)
    (stk,Expression (Const i)) -> do         -- MF TODO: I think this one is not necessary
      setStack stk
      return (trc,Expression (Const i))
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

reduce trc (Observed l s p e) = do
  stk <- gets stack
  (trc',e') <- eval reduce trc e
  case e' of
    Exception msg           -> return (trc',Exception msg)
    Expression (Const i)    -> do
      id <- getUniq
      return (trace (l,s,Value id p (show i)) trc',Expression (Const i))
    Expression (Lambda x e) -> do
      id <- getUniq
      let x' = "_" ++ x; x'' = "__" ++ x
          body = Let (x',Observed l stk (ArgOf id) (Var x'')) 
                     (Apply (Lambda x (Observed l s (ResOf id) e)) x')
          trc''     = trace (l,s,Value id p "\\") trc'
      eval reduce trc'' (Lambda x'' body)

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

type CompGraph = Graph (Vertex String)

tracedEval :: Expr -> (ExprExc Expr,CompGraph)
tracedEval = mkGraph . mkEquations . (evalWith reduce)

disp :: Expr -> IO ()
disp = (display shw) . snd . tracedEval
  where shw :: CompGraph -> String
        shw g = showWith g showVertex showArc
        showVertex = (foldl (++) "") . (map showRecord)
        showRecord = thd
        -- showRecord (lbl,stk,str) = lbl ++ ": " ++ str ++ " (with stack " ++ show stk ++ ")\n"
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
