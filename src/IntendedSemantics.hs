module IntendedSemantics where

import Control.Monad.State
import Prelude hiding (Right)
import Data.Graph.Libgraph
import Data.List (sort,partition,permutations,nub)
import GHC.Exts (sortWith)

--------------------------------------------------------------------------------
-- Expressions

data Expr = CC         Label Judgement Expr
          | Observed   Parent Judgement Expr
          | FunObs     Name Name Parent Judgement Expr
          | Const      Judgement
          | Lambda     Name Expr
          | Apply      Expr Name
          | Var        Name
          | Let        (Name,Expr) Expr
          | Plus       Expr Expr
          | Exception  String
          deriving (Show,Eq)

--------------------------------------------------------------------------------
-- The state.

data Context = Context { trace          :: !Trace
                       , uniq           :: !UID
                       , stack          :: !Stack
                       , heap           :: !Heap
                       , depth          :: !Int
                       , reductionCount :: !Int
                       , reduceLog      :: ![String]
                       , freshVarNames  :: ![Int]
                       }

doLog :: String -> State Context ()
doLog msg = do
  d <- gets depth
  modify $ \cxt -> cxt{reduceLog = (showd d ++ msg ++ "\n") : reduceLog cxt}
  where showd 0 = " "
        showd n = '|' : showd (n-1)

evaluate' :: Expr -> (Expr,Trace,String)
evaluate' redex = (reduct,trace cxt,foldl (++) "" . reverse . reduceLog $ cxt)
  where (reduct,cxt) = runState (eval redex) state0

evaluate :: Expr -> (Expr,Trace)
evaluate redex = (reduct, trace cxt)
  where (reduct,cxt) = runState (eval redex) state0

state0 = Context [] 0 [] [] 0 1 [] [1..]

eval :: (Expr -> State Context Expr)
eval expr = do 
  n <- gets reductionCount
  modify $ \s -> s {reductionCount = n+1}
  if n > 500
    then return (Exception "Giving up after 500 reductions.")
    else do
        d <- gets depth
        modify $ \cxt -> cxt{depth=d+1}
        doLog (show n ++ ": " ++ show expr)
        reduct <- reduce expr
        modify $ \cxt -> cxt{depth=d}
        return reduct

--------------------------------------------------------------------------------
-- Manipulating the heap.

type Name = String
type Heap = [(Name,(Stack,Expr))]

insertHeap :: Name -> (Stack,Expr) -> State Context ()
insertHeap x (_,Exception _) = return ()
insertHeap x e = do
  modify $ \s -> s{heap = (x,e) : (heap s)}
  doLog ("* added " ++ (show (x,e)) ++ " to heap")

deleteHeap :: Name -> State Context ()
deleteHeap x = modify $ \s -> s{heap = filter ((/= x) . fst) (heap s)}

updateHeap x e = do
  deleteHeap x
  insertHeap x e

lookupHeap :: Name -> State Context (Stack,Expr)
lookupHeap x = do 
  me <- fmap (lookup x . heap) get
  case me of
    Nothing -> return ([],Exception ("Lookup '" ++ x ++ "' failed"))
    Just (stk,e) -> return (stk,e)

--------------------------------------------------------------------------------
-- Stack handling: push and call.

type Label = String
type Stack = [Label]

stackIsNow msg = do
  stk <- gets stack
  doLog ("* " ++ msg ++ ": stack is now " ++ show stk)

setStack :: Stack -> State Context ()
setStack stk = do
  modify $ \s -> s {stack = stk}
  stackIsNow "Restore stack from heap"

doPush :: Label -> State Context ()
doPush l = do
  modify $ \s -> s {stack = push l (stack s)}
  stackIsNow $ "Push " ++ l

push :: Label -> Stack -> Stack
push l s
  | l `elem` s = dropWhile (/= l) s
  | otherwise  = l : s

doCall :: Stack -> State Context ()
doCall sLam = do
  stk <- gets stack
  modify $ \s -> s {stack = call (stack s) sLam}
  stackIsNow $ "Call " ++ show stk ++ " " ++ show sLam

-- call sApp sLam ∉ {sApp, SLam} when sLam is not a prefix of sApp.
call :: Stack -> Stack -> Stack
call sApp sLam = sLam' ++ sApp
  where (sPre,sApp',sLam') = commonPrefix sApp sLam

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
-- Reduction rules

reduce :: Expr -> State Context Expr

reduce (Const v) = 
  return (Const v)

reduce (Lambda x e) = 
  return (Lambda x e)

reduce (Let (x,e1) e2) = do
  stk <- gets stack
  insertHeap x (stk,e1)
  eval e2

reduce (Apply f x) = do
  e <- eval f
  case e of 
    (Lambda y e)  -> eval (subst y x e)
    Exception msg -> return (Exception msg)
    _             -> do doLog "Attempt to apply non-Lambda!"
                        doLog (show e)
                        return (Exception "Apply non-Lambda?")

reduce (Var x) = do
  stk       <- gets stack
  (xStk,e') <- lookupHeap x
  setStack xStk                      -- Restore stack as saved on heap
  e         <- eval e'
  xStk'     <- gets stack
  updateHeap x (xStk',e)             -- Update stack (and expression) on heap
  setStack stk                       -- Restore stack as before evaluating
  case e of
     (Lambda _ _) -> do doCall xStk' -- For functions: the current stack is the
                                     -- call-site stack, xStk' is the "lambda"
                                     -- stack. Here we combine the two as Marlow,
                                     -- Solving An Old Problem.
                        fresh e
     _            -> do fresh e

reduce (CC l j e) = do
  stk <- gets stack
  doPush l
  uid <- getUniq
  doTrace (RootEvent l stk uid)
  eval (Observed (Parent uid) j e)

reduce (Observed p j e) = do
  stk <- gets stack
  e' <- eval e
  case e' of
    Exception msg ->
      return (Exception msg)

    -- ObsC rule in paper
    (Const v) -> do
      uid <- getUniq
      let w = v `jand` j
      doTrace (ConstEvent uid p w)
      return (Const w)

    -- ObsL rule in paper
    (Lambda x e) -> do
      i <- getUniq
      doTrace (LamEvent i p)
      x1 <- getFreshVar x
      return (Lambda x1 (FunObs x x1 (Parent i) j e))

    e -> 
      return (Exception $ "Observe undefined: " ++ show e)

-- ObsF rule in paper
reduce (FunObs x x1 p j e) = do
      i  <- getUniq
      doTrace (AppEvent i p)
      x2 <- getFreshVar x
      eval $ Let    (x2,Observed (ArgOf i) Right (Var x1)) 
             {-in-} (Observed (ResOf i) j (Apply (Lambda x e) x2))


reduce (Plus e1 e2) = do
  e1' <- eval e1
  e2' <- eval e2
  case (e1',e2') of
        (Const v1, Const v2) -> return $ Const (v1 `jand` v2)
        (l,r)                -> return (Exception $ "Attempt to sum non-constant values: "
                                                  ++ show l ++ " + " ++ show r)

reduce (Exception msg) = return (Exception msg)

-- reduce e = return (Exception $ "Can't reduce " ++ show e)

--------------------------------------------------------------------------------
-- Substituting variable names.

subst :: Name -> Name -> Expr -> Expr
subst n m (Const v)             = Const v
subst n m (Lambda n' e)         = Lambda (sub n m n') (subst n m e)
subst n m (Apply e n')          = Apply (subst n m e) (sub n m n')
subst n m (Var n')              = Var (sub n m n')
subst n m (Let (n',e1) e2)      = Let ((sub n m n'),(subst n m e1)) (subst n m e2)
subst n m (CC l j e)            = CC l j (subst n m e)
subst n m (Observed p j e)      = Observed p j (subst n m e)
subst n m (FunObs n' n'' p j e) = FunObs (sub n m n') (sub n m n'') p j (subst n m e)
subst n m (Plus e1 e2)          = Plus (subst n m e1) (subst n m e2)

sub :: Name -> Name -> Name -> Name
sub n m n' = if n == n' then m else n'

--------------------------------------------------------------------------------
-- Fresh variable names

fresh :: Expr -> State Context Expr

fresh (Const v) = do
  return (Const v)

fresh (Lambda x e) = do 
  y <- getFreshVar x
  e' <- (fresh . subst x y) e
  return (Lambda y e')

fresh (Let (x,e1) e2) = do 
  y <- getFreshVar x
  e1' <- (fresh . subst x y) e1
  e2' <- (fresh . subst x y) e2
  return $ Let (y,e1') e2'

fresh (Apply f x) = do 
  f' <- fresh f
  return $ Apply f' x

fresh (Var x) =
  return (Var x)

fresh (CC l j e) = do
  e' <- fresh e
  return (CC l j e')

fresh (Observed p j e) = do
  e' <- fresh e
  return (Observed p j e')

fresh (FunObs x x1 p j e) = do
  y <- getFreshVar x
  e' <- (fresh . subst x y) e
  return (FunObs y x1 p j e')

fresh (Exception msg) = return (Exception msg)

fresh (Plus e1 e2) = do
  e1' <- fresh e1
  e2' <- fresh e2
  return (Plus e1' e2')

getFreshVar :: Name -> State Context Name
getFreshVar n = do
  (x:xs) <- gets freshVarNames
  modify $ \cxt -> cxt {freshVarNames=xs}
  return (n ++ show x)

--------------------------------------------------------------------------------
-- Tracing

type Trace = [Event]

data Event
  = RootEvent
    { eventLabel  :: Label
    , eventStack  :: Stack
    , eventUID    :: UID
    } 
  | ConstEvent
    { eventUID    :: UID
    , eventParent :: Parent
    , eventRepr   :: Judgement
    }
  | LamEvent
    { eventUID    :: UID
    , eventParent :: Parent
    }
  | AppEvent
    { eventUID    :: UID
    , eventParent :: Parent
    }    
  deriving (Show,Eq,Ord)

data CompStmt
 = CompStmt
    { stmtLabel  :: Label
    , stmtStack  :: Stack
    , stmtUID    :: UID
    , stmtRepr   :: Judgement
    , stmtRepr'  :: String
    }
 | IntermediateStmt
    { stmtParent :: Parent
    , stmtUID    :: UID
    , stmtRepr   :: Judgement
    , stmtRepr'  :: String
    }
  deriving (Show,Eq,Ord)

type UID = Int

data Parent = Parent UID | ArgOf UID | ResOf UID deriving (Show,Eq,Ord)

getUniq :: State Context UID
getUniq = do
  i <- gets uniq
  modify $ \cxt -> cxt { uniq = i + 1 }
  return i

doTrace :: Event -> State Context ()
doTrace rec = do
  doLog $ "* " ++ show rec
  modify $ \cxt -> cxt{trace = rec : trace cxt}

--------------------------------------------------------------------------------
-- Trace post processing

mkStmts :: (Expr,Trace) -> (Expr,[CompStmt])
mkStmts (reduct,trc) = (reduct,map (successors True chds) roots)
  where isRoot (RootEvent _ _ _) = True
        isRoot _            = False
        (roots,chds) = partition isRoot trc

successors :: Bool -> Trace -> Event -> CompStmt
successors root trc rec = case rec of
        (AppEvent _ _) -> merge root rec $ (suc ArgOf) ++ (suc ResOf)
        (LamEvent _ _) -> merge root rec (suc Parent)
        (RootEvent _ _ _)   -> merge root rec (suc Parent)

  where suc con = map mkStmt $ filter (\chd -> eventParent chd == con (eventUID rec)) trc
        mkStmt (ConstEvent uid p repr) = IntermediateStmt p uid repr (show repr)
        mkStmt chd                     = (successors root' trc chd)
        root' = case rec of (AppEvent _ _) -> False; _ -> root

jand :: Judgement -> Judgement -> Judgement
jand Right Right = Right
jand _     _     = Wrong

merge :: Bool -> Event -> [CompStmt] -> CompStmt

merge _ (RootEvent lbl stk i) []    = CompStmt lbl stk i Right ""
merge _ (RootEvent lbl stk _) (chd:_) = CompStmt lbl stk i r s
  where r = stmtRepr chd
        s = stmtRepr' chd
        i = stmtUID  chd

merge _ (LamEvent i p) []   = IntermediateStmt p i Right ""
merge _ (LamEvent _ p) apps = IntermediateStmt p i r s
  where r = foldl jand Right (map stmtRepr apps)
        (a:pps) = map stmtRepr' apps
        s = (foldl and ("{" ++ a) pps) ++ "}"
        i = head . sort . (map stmtUID) $ apps
        and acc app = acc ++ "; " ++ app

merge _ (AppEvent appUID p) chds = case (length chds) of
  0 -> IntermediateStmt p appUID Right "_ -> _"
  1 -> let res = head chds
           r   = stmtRepr res
           s   = "_ -> " ++ stmtRepr' res
           i   = stmtUID  res
       in IntermediateStmt p i r s
  2 -> let [arg,res] = chds
           r   = case stmtRepr arg of Right -> stmtRepr res; Wrong -> Right
           s   = stmtRepr' arg ++ " -> " ++ stmtRepr' res
           i   = stmtUID res
       in IntermediateStmt p i r s
  _ -> error "merge: Application with multiple arguments?"

--------------------------------------------------------------------------------
-- Debug

data Vertex = RootVertex | Vertex [CompStmt] deriving (Eq,Ord,Show)
type CompGraph = Graph Vertex ()

mkGraph :: (Expr,[CompStmt]) -> (Expr,CompGraph)
mkGraph (reduct,trc) = let (Graph _ vs as) = mapGraph mkVertex (mkGraph' trc)
                           rs              = filter (\(Vertex [c]) -> stmtStack c == []) vs
                           as'             = map (\r -> Arc RootVertex r ()) rs
                       in (reduct, Graph RootVertex (RootVertex:vs) (as' ++ as))

mkGraph' :: [CompStmt] -> Graph CompStmt ()
mkGraph' trace
  | length trace < 1 = error "mkGraph: empty trace"
  | otherwise = Graph (head trace) -- doesn't really matter, replaced above
                       trace
                       (nub $ mkArcs trace)

mkVertex :: CompStmt -> Vertex
mkVertex c = Vertex [c]

-- Implementation of combinations function taken from http://stackoverflow.com/a/22577148/2424911
combinations :: Int -> [a] -> [[a]]
combinations k xs = combinations' (length xs) k xs
  where combinations' n k' l@(y:ys)
          | k' == 0   = [[]]
          | k' >= n   = [l]
          | null l    = []
          | otherwise = map (y :) (combinations' (n - 1) (k' - 1) ys) 
                        ++ combinations' (n - 1) k' ys


permutationsOfLength :: Int -> [a] -> [[a]]
permutationsOfLength x ys
  | length ys < x = []
  | otherwise     = (foldl (++) []) . (map permutations) . (combinations x) $ ys

mkArcs :: [CompStmt] -> [Arc CompStmt ()]
mkArcs cs = callArcs ++ pushArcs
  where pushArcs = map (\[c1,c2] -> Arc c1 c2 ()) ps 
        ps = filter (\[c1,c2] -> pushDependency c1 c2) (permutationsOfLength 2 cs)

        callArcs = foldl (\as [c1,c2,c3] -> (Arc c1 c2 ()) 
                                            : ((Arc c2 c3 ()) : as)) [] ts 
        ts = filter f3 (permutationsOfLength 3 cs)

        f3 [c1,c2,c3] = callDependency c1 c2 c3
        f3 _          = False -- less than 3 statements

nextStack :: CompStmt -> Stack
nextStack rec = push (stmtLabel rec) (stmtStack rec)

pushDependency :: CompStmt -> CompStmt -> Bool
pushDependency p c = nextStack p == stmtStack c

callDependency :: CompStmt -> CompStmt -> CompStmt -> Bool
callDependency pApp pLam c = 
  stmtStack c == call (nextStack pApp) (nextStack pLam)

callDependency2 :: CompStmt -> CompStmt -> CompStmt -> CompStmt -> Bool
callDependency2 pApp pApp' pLam' c = call (nextStack pApp) pLam == stmtStack c
  where pLam = call (nextStack pApp') (nextStack pLam')

callDependency2' :: CompStmt -> CompStmt -> CompStmt -> CompStmt -> Bool
callDependency2' pApp1 pApp2 pLam c = call pApp (nextStack pLam) == stmtStack c
  where pApp = call (nextStack pApp1) (nextStack pApp2)

--------------------------------------------------------------------------------
-- Evaluate and display.

findFaulty' :: CompGraph -> [Vertex]
findFaulty' = findFaulty judgeVertex cat

cat :: [Vertex] -> Vertex
cat = Vertex . (foldl (++) []) . (map unpack)
  where unpack RootVertex  = error "Attempt to merge RootVertex."
        unpack (Vertex cs) = cs

judgeVertex :: Vertex -> Judgement
judgeVertex RootVertex  = Right
judgeVertex (Vertex cs) = foldl (\j v -> j & (stmtRepr v)) Right cs

  where (&) :: Judgement -> Judgement -> Judgement
        Right & Right = Right
        _ & _         = Wrong

debug :: Expr -> IO ()
debug redex = do
  let (reduct,compgraph) = tracedEval redex
  print (findFaulty' compgraph)

debug' :: Expr -> IO ()
debug' redex = do
  let (reduct,compgraph) = tracedEval redex
  print (findFaulty' compgraph)

tracedEval :: Expr -> (Expr,CompGraph)
tracedEval = mkGraph . mkStmts . evaluate

dispTxt :: Expr -> IO ()  
dispTxt = disp' (putStrLn . shw)
  where shw :: CompGraph -> String
        shw g = "\nComputation statements:\n" ++ unlines (map showVertex' $ vertices g)

getLabels :: [Vertex] -> [[Label]]
getLabels = map $ \(Vertex cs) -> (map stmtLabel) cs

-- Requires Imagemagick to be installed.
disp :: Expr -> IO ()
disp = disp' (display shw)
  where shw :: CompGraph -> String
        shw g = showWith g showVertex showArc

dispCollapsed :: Expr -> IO ()
dispCollapsed = disp' (display shw)
  where shw :: CompGraph -> String
        shw g = showWith ((collapse cat) . remove $ g) showVertex showArc

showVertex :: Vertex -> (String,String)
showVertex v = (showVertex' v, "")

showVertex' :: Vertex -> String
showVertex' (Vertex cs) = (foldl (++) "") . (map showCompStmt) $ cs
showVertex' RootVertex  = "RootVertex"

showCompStmt :: CompStmt -> String
showCompStmt rec = stmtLabel rec ++ " = " ++ show (stmtRepr rec) 
                   ++ " (with stack " ++ show (stmtStack rec) ++ ")"
                   ++ "\nfrom " ++ stmtRepr' rec
showArc _ = ""

disp' f expr = do
  putStrLn (messages ++ strc)
  -- writeFile "log" (messages ++ strc)
  f . snd . mkGraph . mkStmts $ (reduct,trc)
  where (reduct,trc,messages) = evaluate' expr
        strc = foldl (\acc s -> acc ++ "\n" ++ s) "\nEvent trace:" (map show $ reverse trc)
