module Context where

import Control.Monad.State
import Data.Graph.Libgraph

-- import qualified Debug.Trace as Debug

--------------------------------------------------------------------------------
-- Stack handling: push and call.

type Label = String
type Stack = [Label]

setStack :: Stack -> Cxt expr ()
setStack stk = modify $ \s -> s {stack = stk}

doPush :: Label -> Cxt expr ()
doPush l = modify $ \s -> s {stack = push l (stack s)}

push :: Label -> Stack -> Stack
push l s
  | l `elem` s = dropWhile (/= l) s
  | otherwise  = l : s

doCall :: Stack -> Cxt expr ()
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

insertHeap :: Name -> (Stack,expr) -> Cxt expr ()
insertHeap x e = modify $ \s -> s{heap = (x,e) : (heap s)}

deleteHeap :: Name -> Cxt expr ()
deleteHeap x = modify $ \s -> s{heap = filter ((/= x) . fst) (heap s)}

lookupHeap :: Name -> Cxt expr (Stack,ExprExc expr)
lookupHeap x = do 
  me <- fmap (lookup x . heap) get
  case me of
    Nothing      -> return ([], Exception ("Lookup '" ++ x ++ "' failed"))
    Just (stk,e) -> return (stk,Expression e)

--------------------------------------------------------------------------------
-- Tracing help.

type Trace value = [Record value]

data Record value = Record
  { recordLabel  :: Label
  , recordStack  :: Stack
  , recordUID    :: UID
  , recordParent :: Parent
  , recordValue  :: value
  } deriving (Show,Eq,Ord)

type UID = Int

data Parent = Root | ArgOf UID | ResOf UID deriving (Show,Eq,Ord)

getUniq :: Cxt expr UID
getUniq = do
  i <- gets uniq
  modify $ \cxt -> cxt { uniq = i + 1 }
  return i


trace :: Record value -> Trace value -> Trace value
trace = (:)

thd :: (a,b,c) -> c
thd (_,_,z) = z

 
successors :: Trace value
           -> (Record value -> Maybe (Record value) -> Maybe (Record value) -> Record value)
           -> Record value -> Record value
successors trc merge rec = merge rec arg res
  where arg = suc ArgOf
        res = suc ResOf
        suc con = case filter (\chd -> recordParent chd == con (recordUID rec)) trc of
          []  -> Nothing
          [chd] -> Just (successors trc merge chd)


--------------------------------------------------------------------------------
-- The state.


type ReduceRule value expr = Trace value -> expr -> Cxt expr (Trace value,ExprExc expr)

data ExprExc expr = Exception String | Expression expr
                  deriving (Show,Eq)

data Context expr = Context { heap           :: !(Heap expr)
                            , stack          :: !Stack
                            , uniq           :: !Int
                            , reductionCount :: !Int
                            }

type Cxt expr res = State (Context expr) res

evalWith :: Show expr
         => ReduceRule value expr -> expr -> (Trace value,ExprExc expr)
evalWith reduce expr = evalState (eval reduce [] expr) (Context [] [] 0 0)

eval :: Show expr =>
        ReduceRule value expr -> Trace value -> expr -> Cxt expr (Trace value,ExprExc expr)
eval reduce trc expr = do 
  n <- gets reductionCount
  modify $ \s -> s {reductionCount = n+1}
  if n > 500
    then return (trc,Exception "Giving up after 500 reductions.")
    else reduce trc expr
    -- else reduce trc (Debug.trace (show n ++ ": " ++ show expr) expr)
