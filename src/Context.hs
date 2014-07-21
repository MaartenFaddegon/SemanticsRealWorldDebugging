module Context where

import Control.Monad.State
import Data.Graph.Libgraph

--------------------------------------------------------------------------------
-- Stack handling: push and call.

type Label = String
type Stack = [Label]
type Record value = (Label,Stack,value)

setStack :: Stack -> State (Context expr) ()
setStack stk = modify $ \s -> s {stack = stk}

doPush :: Label -> State (Context expr) ()
doPush l = modify $ \s -> s {stack = push l (stack s)}

push :: Label -> Stack -> Stack
push l s
  | l `elem` s = dropWhile (/= l) s
  | otherwise  = l : s

doCall :: Stack -> State (Context expr) ()
doCall sLam = modify $ \s -> s {stack = call (stack s) sLam}

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
-- Tracing help.

getUniq :: State (Context expr) Int
getUniq = do
  i <- gets uniq
  modify $ \cxt -> cxt { uniq = i + 1 }
  return i

--------------------------------------------------------------------------------
-- The state.

type Trace value = [Record value]

type ReduceFun value expr = [(Record value)] -> expr -> State (Context expr) (Trace value,ExprExc expr)

data ExprExc expr = Exception String
                  | Expression expr
                  deriving (Show,Eq)

data Context expr = Context { heap           :: !(Heap expr)
                            , uniq           :: !Int
                            , stack          :: Stack
                            , reductionCount :: !Int
                            }

context0 :: Context expr
context0 = Context { heap           = []
                   , stack          = []
                   , uniq           = 0
                   , reductionCount = 0
                   }

-- MF TODO: silly to swap reduct and trace here
evalWith :: ReduceFun value expr -> expr -> (ExprExc expr,Trace value)
evalWith reduce expr = let (trc,reduct) = evalState (eval reduce [] expr) context0 in (reduct,trc)

eval :: ReduceFun value expr -> Trace value -> expr 
         -> State (Context expr) (Trace value,ExprExc expr)
eval reduce trc expr = do 
  n <- gets reductionCount
  modify $ \s -> s {reductionCount = n+1}
  if n > 500
    then return (trc,Exception "Giving up after 500 reductions.")
    else reduce trc expr
