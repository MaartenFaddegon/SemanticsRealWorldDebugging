module Context where

import Control.Monad.State
import Data.Graph.Libgraph
import qualified Debug.Trace as Debug

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
    Nothing      -> return ([], Exception ("Lookup '" ++ x ++ "' failed"))
    Just (stk,e) -> return (stk,Expression e)

--------------------------------------------------------------------------------
-- The state.

type Trace record = [record]

type ReduceFun record expr = Stack -> [record] -> expr 
                      -> State (Context expr) (Stack,Trace record,ExprExc expr)

data ExprExc expr = Exception String
                  | Expression expr
                  deriving (Show,Eq)

data Context expr = Context { heap        :: !(Heap expr)
                            , reductionCount :: !Int
                            }

estate0 :: Context expr
estate0 = Context heap0 0

evalE' :: Show expr
       => ReduceFun record expr -> expr -> (Stack,Trace record,ExprExc expr)
evalE' reduce e = evalState f estate0
  where f = evalUpto reduce [] [] e

evalE :: Show expr => ReduceFun record expr -> expr -> Trace record
evalE reduce e = let (_,t,_) = evalE' reduce e in t

evalUpto :: Show expr
         => ReduceFun record expr ->  Stack -> Trace record -> expr 
         -> State (Context expr) (Stack,Trace record,ExprExc expr)
evalUpto reduce stk trc expr = do 
  n <- gets reductionCount
  modify $ \s -> s {reductionCount = n+1}
  if n > 500
    then return (stk,trc,Exception "Giving up after 500 reductions.")
    else reduce stk trc (Debug.trace ("reduce " ++ show expr) expr)


