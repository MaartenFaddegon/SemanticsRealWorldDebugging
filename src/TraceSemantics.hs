module TraceSemantics where

import Control.Monad.State
import Data.Graph.Libgraph
import Data.List (sort,partition,permutations)
import qualified Debug.Trace as Debug

--------------------------------------------------------------------------------
-- Expressions

data Expr = ACC        Label Expr
          | Observed   Parent Expr
          | FunObs     Name Name Parent Expr
          | Const      Int
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

reduce (ACC l e) = do
  stk <- gets stack
  doPush l
  uid <- getUniq
  doTrace (Root l stk uid)
  eval (Observed (Parent uid) e)

reduce (Observed p e) = do
  stk <- gets stack
  e' <- eval e
  case e' of
    Exception msg ->
      return (Exception msg)

    -- ObsC rule in paper
    (Const v) -> do
      uid <- getUniq
      doTrace (ConstEvent uid p (show v))
      return e'

    -- ObsL rule in paper
    (Lambda x e) -> do
      i <- getUniq
      doTrace (LamEvent i p)
      x1 <- getFreshVar x
      return (Lambda x1 (FunObs x x1 (Parent i) e))

    e -> 
      return (Exception $ "Observe undefined: " ++ show e)

-- ObsF rule in paper
reduce (FunObs x x1 p e) = do
      i  <- getUniq
      doTrace (AppEvent i p)
      x2 <- getFreshVar x
      eval $ Let    (x2,Observed (ArgOf i) (Var x1)) 
             {-in-} (Observed (ResOf i) (Apply (Lambda x e) x2))


reduce (Plus e1 e2) = do
  e1' <- eval e1
  e2' <- eval e2
  case (e1',e2') of
        (Const v1, Const v2) -> return $ Const (v1 + v2)
        (l,r)                -> return (Exception $ "Attempt to sum non-constant values: "
                                                  ++ show l ++ " + " ++ show r)

reduce (Exception msg) = return (Exception msg)

-- reduce e = return (Exception $ "Can't reduce " ++ show e)

--------------------------------------------------------------------------------
-- Substituting variable names.

subst :: Name -> Name -> Expr -> Expr
subst n m (Const v)           = Const v
subst n m (Lambda n' e)       = Lambda (sub n m n') (subst n m e)
subst n m (Apply e n')        = Apply (subst n m e) (sub n m n')
subst n m (Var n')            = Var (sub n m n')
subst n m (Let (n',e1) e2)    = Let ((sub n m n'),(subst n m e1)) (subst n m e2)
subst n m (ACC l e)           = ACC l (subst n m e)
subst n m (Observed p e)      = Observed p (subst n m e)
subst n m (FunObs n' n'' p e) = FunObs (sub n m n') (sub n m n'') p (subst n m e)
subst n m (Plus e1 e2)        = Plus (subst n m e1) (subst n m e2)

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

fresh (ACC l e) = do
  e' <- fresh e
  return (ACC l e')


fresh (Observed p e) = do
  e' <- fresh e
  return (Observed p e')

fresh (FunObs x x1 p e) = do
  y <- getFreshVar x
  e' <- (fresh . subst x y) e
  return (FunObs y x1 p e')

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
  = Root
    { eventLabel  :: Label
    , eventStack  :: Stack
    , eventUID    :: UID
    } 
  | ConstEvent
    { eventUID    :: UID
    , eventParent :: Parent
    , eventRepr   :: String
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
    , stmtRepr   :: String
    }
 | IntermediateStmt
    { stmtParent :: Parent
    , stmtUID    :: UID
    , stmtRepr   :: String
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
  where isRoot (Root _ _ _) = True
        isRoot _            = False
        (roots,chds) = partition isRoot trc

successors :: Bool -> Trace -> Event -> CompStmt
successors root trc rec = case rec of
        (AppEvent _ _) -> merge root rec $ (suc ArgOf) ++ (suc ResOf)
        (LamEvent _ _) -> merge root rec (suc Parent)
        (Root l s _)   -> merge root rec (suc Parent)

  where suc con = map mkStmt $ filter (\chd -> eventParent chd == con (eventUID rec)) trc
        mkStmt (ConstEvent uid p repr) = case rec of
          (Root _ _ _) -> IntermediateStmt p uid ("= " ++ repr)
          _            -> IntermediateStmt p uid repr
	mkStmt chd                     = (successors root' trc chd)
	root' = case rec of (AppEvent _ _) -> False; _ -> root

oldestUID :: [UID] -> UID
oldestUID = head . sort

merge :: Bool -> Event -> [CompStmt] -> CompStmt

merge _ (Root lbl stk i) []    = CompStmt lbl stk i "_"
merge _ (Root lbl stk _) [chd] = CompStmt lbl stk i (lbl ++ " " ++ r)
  where r = stmtRepr chd
        i = stmtUID  chd
merge _ (Root lbl stk i) _     = error "merge: Root with multiple children?"

merge _ (LamEvent i p) []   = IntermediateStmt p i "_"
merge _ (LamEvent _ p) [a]  = IntermediateStmt p (stmtUID a) (stmtRepr a)
merge _ (LamEvent _ p) apps = IntermediateStmt p i r
  where (a:pps)     = map stmtRepr apps
        r           = (foldl and ("{" ++ a) pps) ++ "}"
        i           = head . sort . (map stmtUID) $ apps
        and acc app = acc ++ "; " ++ app

merge t (AppEvent _ p) chds = case (length chds) of
  0 -> error "merge: Application with neither result nor argument?"
  1 -> let res = head chds
           r   = mkStmt "_" (stmtRepr res)
           i   = stmtUID  res
       in IntermediateStmt p i r
  2 -> let [arg,res] = chds
           r   = mkStmt (stmtRepr arg) (stmtRepr res)
           i   = stmtUID res
       in IntermediateStmt p i r
  _ -> error "merge: Application with multiple arguments?"
  where mkStmt arg res = pre ++ arg ++ inf ++ res ++ post
        pre  = if t then "" else "(\\"
        inf  = if t then " = " else " -> "
        post = if t then "" else ")"

--------------------------------------------------------------------------------
-- Debug

data Dependency = PushDep | CallDep Int deriving (Eq,Show)

instance Ord Dependency where
  compare PushDep (CallDep _)     = LT
  compare (CallDep _) PushDep     = GT
  compare (CallDep n) (CallDep m) = compare n m
  compare PushDep PushDep         = EQ

type CompGraph = Graph [CompStmt] Dependency

mkGraph :: (Expr,[CompStmt]) -> (Expr,CompGraph)
mkGraph (reduct,trc) = (reduct,mapGraph (\r->[r]) (mkGraph' trc))

mkGraph' :: [CompStmt] -> Graph CompStmt Dependency
mkGraph' trace
  | length trace < 1 = error "mkGraph: empty trace"
  | length roots < 1 = error "mkGraph: no root"
  | otherwise = Graph (head roots)
                       trace
                       (mkArcs trace)
                       -- (nubMin $ foldr (\r as -> as ++ (arcsFrom r trace)) [] trace)
  where roots = filter isRoot trace
        isRoot CompStmt{stmtStack=s} = s == []
        isRoot _                              = error "mkGraph': Leftover intermediate stmt?"

nubMin :: (Eq a, Ord b) => [Arc a b] -> [Arc a b]
nubMin l = nub' l []
  where

    nub' [] _           = []
    nub' (x:xs) ls = let (sat,unsat) = partition (equiv x) ls
                     in case sat of
                        [] -> x : nub' xs (x:ls)
                        _  -> nub' xs ((minimum' $ x:sat) : unsat )

    minimum' as = (head as) { arc = minimum (map arc as) }

    equiv (Arc v w _) (Arc x y _) = v == x && w == y

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
permutationsOfLength x = (foldl (++) []) . (map permutations) . (combinations x)

mkArcs :: [CompStmt] -> [Arc CompStmt Dependency]
mkArcs cs = callArcs ++ pushArcs
  where pushArcs = map (\[c1,c2]    -> Arc c1 c2 PushDep) ps 
        callArcs = foldl (\as [c1,c2,c3] -> (Arc c1 c2 $ CallDep 1) 
                                            : ((Arc c2 c3 $ CallDep 1) : as)) [] ts 
        ps = filter (\[c1,c2]    -> pushDependency c1 c2)    (permutationsOfLength 2 cs)
        ts = filter (\[c1,c2,c3] -> callDependency c1 c2 c3) (permutationsOfLength 3 cs)

arcsFrom :: CompStmt -> [CompStmt] -> [Arc CompStmt Dependency]
arcsFrom src trc =  ((map (\tgt -> Arc src tgt PushDep)) . (filter isPushArc) $ trc)
                 ++ ((map (\tgt -> Arc src tgt (CallDep 1))) . (filter isCall1Arc) $ trc)

                 -- MF TODO: do we need level-2 arcs?
                 -- ++ ((map (\tgt -> Arc src tgt (CallDep 2))) . (filter isCall2Arc) $ trc)
                 

  where isPushArc = pushDependency src
        
        isCall1Arc = anyOf $ map (flip callDependency src) trc
                     -- anyOf $ map (callDependency src) trc

        isCall2Arc = anyOf $  apmap (map (callDependency2 src) trc) trc
                           ++ apmap (map (callDependency2' src) trc) trc

        anyOf :: [a->Bool] -> a -> Bool
        anyOf ps x = or (map (\p -> p x) ps)

        apmap :: [a->b] -> [a] -> [b]
        apmap fs xs = foldl (\acc f -> acc ++ (map f xs)) [] fs

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
-- Examples.

tracedEval :: Expr -> (Expr,CompGraph)
tracedEval = mkGraph . mkStmts . evaluate

dispTxt :: Expr -> IO ()  
dispTxt = disp' (putStrLn . shw)
  where shw :: CompGraph -> String
        shw g = "\nComputation statements:\n" ++ unlines (map showVertex' $ vertices g)

-- Requires Imagemagick to be installed.
disp :: Expr -> IO ()
disp = disp' (display shw)
  where shw :: CompGraph -> String
        shw g = showWith g showVertex showArc

showVertex :: [CompStmt] -> (String,String)
showVertex v = (showVertex' v, "")

showVertex' :: [CompStmt] -> String
showVertex' = (foldl (++) "") . (map showCompStmt)

showCompStmt :: CompStmt -> String
showCompStmt (CompStmt l s i r) = r ++ " (with stack " ++ show s ++ ")"
showArc (Arc _ _ dep)  = show dep

disp' f expr = do
  putStrLn (messages ++ strc)
  -- writeFile "log" (messages ++ strc)
  f . snd . mkGraph . mkStmts $ (reduct,trc)
  where (reduct,trc,messages) = evaluate' expr
        strc = foldl (\acc s -> acc ++ "\n" ++ s) "\nEvent trace:" (map show $ reverse trc)
