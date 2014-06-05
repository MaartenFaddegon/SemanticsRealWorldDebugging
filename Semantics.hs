module Semantics (Stack,push,call) where
import Control.Monad.State

--------------------------------------------------------------------------------
-- Stack handling: push and call

type Label = String
type Stack = [Label]

push :: Label -> Stack -> Stack
push l s
  | l `elem` s = dropWhile (/= l) s
  | otherwise  = l : s

call :: Stack -> Stack -> Stack
call sApp sLam = foldr push sPre sLam'
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
-- Tracing.

type Trace = [(Label,Stack,Value)]

trace :: (Label,Stack,Value) -> Trace -> Trace
trace = (:)

--------------------------------------------------------------------------------
-- Expressions.

type Name = String

data Value = Correct | Wrong deriving Show

data Expr = Const
          | Lambda Name Expr
          | Apply Expr Name
          | Var Name
          | Let (Name,Expr) Expr
          | CorrectExpr Label Expr
          | FaultyExpr Label Expr
          deriving Show

--------------------------------------------------------------------------------
-- The reduction rules.

eval :: Stack -> Expr -> E (Stack, Expr)

eval stk Const = return (stk, Const)

eval stk (Lambda x e) = return (stk, Lambda x e)

eval stk (CorrectExpr l e) = eval (push l stk) e

eval stk (FaultyExpr l e)  = eval (push l stk) e

eval stk (Let (x,e1) e2) = do
  insertHeap x (stk,e2)
  eval stk e2

eval stk (Apply f x) = do
  (stk_lam, Lambda y e) <- eval stk f
  eval stk_lam (subst y x e)

eval stk (Var x) = do
  r <- lookupHeap x
  case r of
    (stk',Const)  -> return (stk',Const)
    (stk',Lambda y e) -> return (call stk stk', Lambda y e)
    (stk',e) -> do
      deleteHeap x
      (stkv, v) <- eval stk' e
      insertHeap x (stkv,e)
      eval stk (Var x)

--------------------------------------------------------------------------------
-- The state.

data EState = EState { theHeap      :: [(Name,(Stack,Expr))]
                     -- , theFreshVars :: [Name]
                     }

type E a = State EState a

evalE :: Expr -> (Stack, Expr)
evalE e = evalState (eval [] e) (EState [])

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
-- Tests.

test1 = evalE $ Const

test2 = evalE $ FaultyExpr "x" Const
