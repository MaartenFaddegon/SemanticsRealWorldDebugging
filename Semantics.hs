module Semantics (Stack,push,call) where
import Control.Monad.State
import Prelude hiding (Right)

--------------------------------------------------------------------------------
-- Stack handling: push and call

type Label = String
type Stack = [Label]

push :: Label -> Stack -> Stack
push l s
  | l `elem` s = dropWhile (/= l) s
  | otherwise  = l : s

call :: Stack -> Stack -> Stack
call sApp sLam = sApp ++ sLam'
  where (sPre,sApp',sLam') = commonPrefix sApp sLam

commonPrefix :: Stack -> Stack -> (Stack, Stack, Stack)
commonPrefix sApp sLam
  = let (sPre,sApp',sLam') = span2 (==) (reverse sApp) (reverse sLam)
    in (reverse sPre, reverse sApp', reverse sLam') 

span2 :: (a -> a -> Bool) -> [a] -> [a] -> ([a], [a], [a])
span2 f = s f []
  where s _ pre [] ys = (pre,[],ys)
        s _ pre xs [] = (pre,xs,[])
        s f pre xs@(x:xs') ys@(y:ys') 
          | f x y     = s f (x:pre) xs' ys'
          | otherwise = (pre,xs,ys)

--------------------------------------------------------------------------------
-- Expressions.

type Name = String

data Expr = Const
          | Lambda Name Expr
          | Apply Expr Name
          | Var Name
          | Let (Name,Expr) Expr
          | CorrectExpr Label Expr
          | FaultyExpr Label Expr
          | Observed Label Stack Expr
          deriving Show

--------------------------------------------------------------------------------
-- The reduction rules.

eval :: Stack -> Trace -> Expr -> E (Stack,Trace,Expr)

eval stk trc Const = return (stk,trc,Const)

eval stk trc (Lambda x e) = return (stk,trc,Lambda x e)

eval stk trc (CorrectExpr l e) = eval (push l stk) trc (Observed l stk e)

eval stk trc (FaultyExpr l e)  = eval (push l stk) (trace (l,stk,Wrong) trc) e

eval stk trc (Let (x,e1) e2) = do
  insertHeap x (stk,e2)
  eval stk trc e2

eval stk trc (Apply f x) = do
  (stk_lam, trc_lam, Lambda y e) <- eval stk trc f
  eval stk_lam trc_lam (subst y x e)

eval stk trc (Var x) = do
  r <- lookupHeap x
  case r of
    (stk',Const)  -> return (stk',trc,Const)
    (stk',Lambda y e) -> return (call stk stk',trc,Lambda y e)
    (stk',e) -> do
      deleteHeap x
      (stkv,trcv,v) <- eval stk' trc e
      insertHeap x (stkv,e)
      eval stk trcv (Var x) -- Notice how we retain the trace but swap back the stack

eval stk trc (Observed l s e) = do
  case e of Const              -> return (stk,trace (l,s,Right) trc, Const)
            (FaultyExpr l' e') -> eval stk (trace (l,s,Wrong) trc) (FaultyExpr l' e')
            _ -> do
              (stk',trc',e') <- eval stk trc e
              return (stk',trc',(Observed l s e'))

--------------------------------------------------------------------------------
-- The state.

data EState = EState { theHeap      :: [(Name,(Stack,Expr))]
                     -- , theFreshVars :: [Name]
                     }

type E a = State EState a

evalE' :: Expr -> (Stack,Trace,Expr)
evalE' e = evalState (eval [] [] e) (EState [])

evalE :: Expr -> Trace
evalE e = let (_,t,_) = evalE' e in t

--------------------------------------------------------------------------------
-- Manipulating the heap

insertHeap :: Name -> (Stack,Expr) -> E ()
insertHeap x e = modify $ \s -> s{theHeap = (x,e) : (theHeap s)}

deleteHeap :: Name -> E ()
deleteHeap x = modify $ \s -> s{theHeap = filter ((/= x) . fst) (theHeap s)}

lookupHeap :: Name -> E (Stack,Expr)
lookupHeap x = do 
  me <- fmap (lookup x . theHeap) get
  case me of
    Nothing -> return ([], Const) -- Keep going with a Const if we find nothing.
    Just e  -> return e

--------------------------------------------------------------------------------
-- Substituting variable names.

subst :: Name -> Name -> Expr -> Expr
subst = undefined

--------------------------------------------------------------------------------
-- Tracing.
--
-- A recorded value is Right or Wrong.

type Record = (Label,Stack,Correctness)

type Trace = [Record]

data Correctness = Right | Wrong deriving (Show,Eq)

trace :: Record -> Trace -> Trace
trace = (:)

--------------------------------------------------------------------------------
-- Algorithmic debugging from a trace.

type Node  = Record
data Arc   = Arc Node Node deriving Show
type Graph = ([Node],[Arc])

mkGraph :: Trace -> Graph
mkGraph trace = (trace,foldr (\r as -> as ++ (arcsFrom r trace)) [] trace)

arcsFrom :: Record -> Trace -> [Arc]
arcsFrom src = (map (Arc src)) . (filter (src `couldDependOn`))

couldDependOn :: Record -> Record -> Bool
couldDependOn (l,s,_) (_,t,_) = push l s == t

children :: Node -> Graph -> [Node]
children n = (map (\(Arc _ tgt) -> tgt)) . (filter (\(Arc src _) -> src == n)) . snd

faultyNodes :: Graph -> [Label]
faultyNodes (ns,as) = (map (\(l,_,_) -> l)) . (filter faulty) $ ns
        where faulty (_,_,Right) = False
              faulty n = [] == filter isWrong (children n (ns,as))

isWrong :: Node -> Bool
isWrong (_,_,Wrong) = True
isWrong _           = False

--------------------------------------------------------------------------------
-- Tests.


expr1 = CorrectExpr "y" (FaultyExpr "x" Const)

test1 = faultyNodes . mkGraph .evalE $ expr1
