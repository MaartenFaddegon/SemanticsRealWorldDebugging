module Runtime where

import Control.Monad.State
import Data.Graph.Libgraph


--------------------------------------------------------------------------------
-- Stack handling: push and call.

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
-- The state.

type ReduceFun expr = Stack -> Trace -> expr 
                      -> State (Context expr) (Stack,Trace,ExprExc expr)

data ExprExc expr = Exception String
                  | Expression expr
                  deriving Eq

data Context expr = Context { heap        :: !(Heap expr)
                            , reductionCount :: !Int
                            }

estate0 :: Context expr
estate0 = Context heap0 0

evalE' :: ReduceFun expr -> expr -> (Stack,Trace,ExprExc expr)
evalE' eval e = evalState f estate0
  where f = evalUpto eval [] [] e

evalE :: ReduceFun expr -> expr -> Trace
evalE eval e = let (_,t,_) = evalE' eval e in t

evalUpto :: ReduceFun expr ->  Stack -> Trace -> expr 
         -> State (Context expr) (Stack,Trace,ExprExc expr)
evalUpto eval stk trc expr = do 
  n <- gets reductionCount
  modify $ \s -> s {reductionCount = n+1}
  if n > 500
    then return (stk,trc,Exception "Giving up after 500 reductions.")
    else eval stk trc expr

--------------------------------------------------------------------------------
-- Manipulating the heap.

type Name = String
type Heap expr = [(Name,(Stack,expr))]

heap0 :: Heap expr
heap0 = []

insertHeap :: Name -> (Stack,expr) -> State (Context expr) ()
insertHeap x e = modify $ \s -> s{heap = (x,e) : (heap s)}

deleteHeap :: Name -> State (Context expr) ()
deleteHeap x = modify $ \s -> s{heap = filter ((/= x) . fst) (heap s)}

lookupHeap :: Name -> State (Context expr) (Stack,ExprExc expr)
lookupHeap x = do 
  me <- fmap (lookup x . heap) get
  case me of
    Nothing      -> return ([], Exception "Lookup failed")
    Just (stk,e) -> return (stk,Expression e)

--------------------------------------------------------------------------------
-- Tracing.
--
-- A recorded value is Right or Wrong.

data Value  = Right | Wrong       deriving (Show,Eq,Ord)
type Record = (Label,Stack,Value)
type Trace  = [Record]

trace :: Record -> Trace -> Trace
trace = (:)
