module Context where

import Control.Monad.State
import Data.Graph.Libgraph

import qualified Debug.Trace as Debug

--------------------------------------------------------------------------------
-- Stack handling: push and call.

type Label = String
type Stack = [Label]

setStack :: Stack -> Cxt expr repr ()
setStack stk = modify $ \s -> s {cxtStack = stk}

doPush :: Label -> Cxt expr repr ()
doPush l = modify $ \s -> s {cxtStack = push l (cxtStack s)}

push :: Label -> Stack -> Stack
push l s
  | l `elem` s = dropWhile (/= l) s
  | otherwise  = l : s

doCall :: Stack -> Cxt expr repr ()
doCall sLam = modify $ \s -> s {cxtStack = call (cxtStack s) sLam}

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
insertHeap x e = modify $ \s -> s{cxtHeap = (x,e) : (cxtHeap s)}

deleteHeap :: Name -> Cxt expr repr ()
deleteHeap x = modify $ \s -> s{cxtHeap = filter ((/= x) . fst) (cxtHeap s)}

lookupHeap :: Show expr => Name -> Cxt expr repr (Stack,ExprExc expr)
lookupHeap x = do 
  me <- fmap (lookup x . cxtHeap) get
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
  i <- gets cxtUniq
  modify $ \cxt -> cxt { cxtUniq = i + 1 }
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

type ReduceRule expr repr = expr -> Cxt expr repr (ExprExc expr)

data ExprExc expr = Exception String | Expression expr
                  deriving (Show,Eq)

data Context expr repr 
  = Context { cxtHeap   :: !(Heap expr)
            , cxtStack  :: !Stack
            , cxtUniq   :: !Int
            , cxtTrace  :: !(Trace repr)

            , cxtCount  :: !Int          -- Number of expressions reduced
            , cxtDepth  :: !Int          -- At what subexrpression-level are we reducing
            , cxtLog    :: ![String]     -- Sequential log of redexes and trace messages
            }

type Cxt expr repr res = State (Context expr repr) res

evalWith' :: Show expr
          => ReduceRule expr repr -> expr -> (Trace repr,ExprExc expr,String)
evalWith' reduce redex =
  let (res,cxt) = runState (eval reduce redex) (Context [] [] 1 [] 0 0 [])
  in (cxtTrace cxt, res, foldl (++) "" . reverse . cxtLog $ cxt)

evalWith :: Show expr
         => ReduceRule expr repr -> expr -> (Trace repr,ExprExc expr)
evalWith reduce expr = let (trc,reduct,_) = evalWith' reduce expr in (trc,reduct)

eval :: Show expr =>
        ReduceRule expr repr -> expr -> Cxt expr repr (ExprExc expr)
eval reduce expr = do 
  n <- gets cxtCount
  modify $ \s -> s {cxtCount = n+1}
  if n > 500
    then return (Exception "Giving up after 500 reductions.")
    else do
        d <- gets cxtDepth
        modify $ \cxt -> cxt{cxtDepth=d+1}
        doLog (showd d ++ show n ++ ": " ++ show expr)
        reduct <- reduce expr
        modify $ \cxt -> cxt{cxtDepth=d}
        return reduct
  where showd 0 = ""
        showd n = '|' : showd (n-1)
