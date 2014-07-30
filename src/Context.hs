module Context where

import Control.Monad.State
import Data.Graph.Libgraph

import qualified Debug.Trace as Debug

--------------------------------------------------------------------------------
-- Stack handling: push and call.

type Label = String
type Stack = [Label]

setStack :: Stack -> Cxt expr repr ()
setStack stk = modify $ \s -> s {stack = stk}

doPush :: Label -> Cxt expr repr ()
doPush l = modify $ \s -> s {stack = push l (stack s)}

push :: Label -> Stack -> Stack
push l s
  | l `elem` s = dropWhile (/= l) s
  | otherwise  = l : s

doCall :: Stack -> Cxt expr repr ()
doCall sLam = modify $ \s -> s {stack = call (stack s) sLam}

call :: Stack -> Stack -> Stack
-- MF TODO: look into this, call sApp sLam = sApp ++ sLam'
call sApp sLam =
       sNew

-- call sApp sLam = sNew
  where (sPre,sApp',sLam') = commonPrefix sApp sLam
        sNew = sLam' ++ sApp

commonPrefix :: Stack -> Stack -> (Stack, Stack, Stack)
commonPrefix sApp sLam
  = let (sPre,sApp',sLam') = span2 (==) (reverse sApp) (reverse sLam)
    in (sPre, reverse sApp', reverse sLam') 

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

insertHeap :: Name -> (Stack,expr) -> Cxt expr repr ()
insertHeap x e = modify $ \s -> s{heap = (x,e) : (heap s)}

deleteHeap :: Name -> Cxt expr repr ()
deleteHeap x = modify $ \s -> s{heap = filter ((/= x) . fst) (heap s)}

lookupHeap :: Show expr => Name -> Cxt expr repr (Stack,WithExc expr)
lookupHeap x = do 
  me <- fmap (lookup x . heap) get
  case me of
    Nothing      -> return ([], Exception ("Lookup '" ++ x ++ "' failed"))
    Just (stk,e) -> return (stk,Expression e)
    -- Just (stk,e) -> return (stk,Debug.trace ("lookup " ++ x ++ " = " ++ show e)Expression e)

--------------------------------------------------------------------------------
-- Tracing help.

type Trace repr = [Record repr]

data Record repr = Record
  { recordLabel  :: Label
  , recordStack  :: Stack
  , recordUID    :: UID
  , recordParent :: Parent
  , recordRepr   :: repr
  } deriving (Show,Eq,Ord)

type UID = Int

data Parent = Root | ArgOf UID | ResOf UID deriving (Show,Eq,Ord)

getUniq :: Cxt expr repr UID
getUniq = do
  i <- gets uniq
  modify $ \cxt -> cxt { uniq = i + 1 }
  return i

trace :: Show repr => Record repr -> Cxt expr repr ()
trace rec = do
  doLog $ " * " ++ show rec
  modify $ \cxt -> cxt{cxtTrace = rec : cxtTrace cxt}

thd :: (a,b,c) -> c
thd (_,_,z) = z

-- MF TODO: in some weird cases it seems to happen that there are multiple children.
-- I now just pick the first put that may not be what we really want. This
-- may be related to our not so sophisticated scope rules (should we implement
-- freshen?).
successors :: Trace repr
           -> (Record repr -> Maybe (Record repr) -> Maybe (Record repr) -> Record repr)
           -> Record repr -> Record repr
successors trc merge rec = merge rec arg res
  where arg = suc ArgOf
        res = suc ResOf
        suc con = case filter (\chd -> recordParent chd == con (recordUID rec)) trc of
          []    -> Nothing
          chd:_ -> Just (successors trc merge chd)


--------------------------------------------------------------------------------
-- Logging.

doLog :: String -> Cxt expr repr ()
doLog msg = modify $ \cxt -> cxt{cxtLog = (msg ++ "\n") : cxtLog cxt}

--------------------------------------------------------------------------------
-- The state.

type ReduceRule expr repr = expr -> Cxt expr repr (WithExc expr)

data WithExc expr = Exception String | Expression expr
                  deriving (Show,Eq)

data Context expr repr 
  = Context { heap           :: !(Heap expr)
            , stack          :: !Stack
            , uniq           :: !Int
            , reductionCount :: !Int
            , depth          :: !Int
            , cxtTrace       :: !(Trace repr)
            , cxtLog         :: ![String]
            }

type Cxt expr repr res = State (Context expr repr) res

evalWith' :: Show expr
          => ReduceRule expr repr -> expr -> (Trace repr,WithExc expr,String)
evalWith' reduce redex =
  let (res,cxt) = runState (eval reduce redex) (Context [] [] 0 0 1 [] [])
  in (cxtTrace cxt, res, foldl (++) "" . reverse . cxtLog $ cxt)

evalWith :: Show expr
         => ReduceRule expr repr -> expr -> (Trace repr,WithExc expr)
evalWith reduce expr = let (trc,reduct,_) = evalWith' reduce expr in (trc,reduct)

eval :: Show expr =>
        ReduceRule expr repr -> expr -> Cxt expr repr (WithExc expr)
eval reduce expr = do 
  n <- gets reductionCount
  modify $ \s -> s {reductionCount = n+1}
  if n > 500
    then return (Exception "Giving up after 500 reductions.")
    else do
        d <- gets depth
        modify $ \cxt -> cxt{depth=d+1}
        doLog (showd d ++ show n ++ ": " ++ show expr)
        reduct <- reduce expr
        modify $ \cxt -> cxt{depth=d}
        return reduct
  where showd 0 = ""
        showd n = '|' : showd (n-1)
