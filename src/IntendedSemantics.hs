module IntendedSemantics where

import Control.Monad.State
import Prelude hiding (Right)
import Data.Graph.Libgraph
import Data.List (sort)
import GHC.Exts (sortWith)
import Data.List (partition)

--------------------------------------------------------------------------------
-- Expressions

data Expr = ACCCorrect Label Expr
          | ACCFaulty  Label Expr
          | Observed   Parent Expr
          | FunObs     Name Name Parent Expr
          | Const      Judgement
          | Lambda     Name Expr
          | Apply      Expr Name
          | Var        Name
          | Let        (Name,Expr) Expr
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

reduce (ACCCorrect l e) = do
  stk <- gets stack
  doPush l
  uid <- getUniq
  doTrace (Root l stk uid)
  eval (Observed (Parent uid) e)

reduce (ACCFaulty l e) = do
  stk <- gets stack
  doPush l
  uid <- getUniq; uidc <- getUniq
  doTrace (Root l stk uid); doTrace (ConstEvent uidc (Parent uid) Wrong)
  r <- eval e
  case r of
    (Const jmt) -> return (Const Wrong)
    _           -> return r

reduce (Observed p e) = do
  stk <- gets stack
  e' <- eval e
  case e' of
    Exception msg ->
      return (Exception msg)

    -- ObsC rule in paper
    (Const v) -> do
      uid <- getUniq
      doTrace (ConstEvent uid p v)
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
subst n m (ACCCorrect l e)    = ACCCorrect l (subst n m e)
subst n m (ACCFaulty l e)     = ACCFaulty l (subst n m e)
subst n m (Observed p e)      = Observed p (subst n m e)
subst n m (FunObs n' n'' p e) = FunObs (sub n m n') (sub n m n'') p (subst n m e)

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

fresh (ACCCorrect l e) = do
  e' <- fresh e
  return (ACCCorrect l e')

fresh (ACCFaulty l e) = do
  e' <- fresh e
  return (ACCFaulty l e')

fresh (Observed p e) = do
  e' <- fresh e
  return (Observed p e')

fresh (FunObs x x1 p e) = do
  y <- getFreshVar x
  e' <- (fresh . subst x y) e
  return (FunObs y x1 p e')

fresh (Exception msg) = return (Exception msg)

getFreshVar :: Name -> State Context Name
getFreshVar n = do
  (x:xs) <- gets freshVarNames
  modify $ \cxt -> cxt {freshVarNames=xs}
  return (n ++ show x)

--------------------------------------------------------------------------------
-- Tracing

data Judgement  = Right | Wrong deriving (Eq,Ord)

instance Show Judgement where
  show Right = "☺"
  show Wrong = "☹"

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
    }
 | IntermediateStmt
    { stmtParent :: Parent
    , stmtUID    :: UID
    , stmtRepr   :: Judgement
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
        (Root _ _ _)   -> merge root rec (suc Parent)

  where suc con = map mkStmt $ filter (\chd -> eventParent chd == con (eventUID rec)) trc
        mkStmt (ConstEvent uid p repr) = IntermediateStmt p uid repr
	mkStmt chd                     = (successors root' trc chd)
	root' = case rec of (AppEvent _ _) -> False; _ -> root

oldestUID :: [UID] -> UID
oldestUID = head . sort

merge :: Bool -> Event -> [CompStmt] -> CompStmt

merge _ (Root lbl stk i) []    = CompStmt lbl stk i Right
merge _ (Root lbl stk _) [chd] = CompStmt lbl stk i r
  where r = stmtRepr chd
        i = stmtUID  chd
merge _ (Root lbl stk i) _     = error "merge: Root with multiple children?"

merge _ (LamEvent i p) []   = IntermediateStmt p i Right
merge _ (LamEvent _ p) apps = IntermediateStmt p i r
  where r = foldl and Right (map stmtRepr apps)
        i = head . sort . (map stmtUID) $ apps
        and Right Right = Right
        and _     _     = Wrong

merge _ (AppEvent _ p) chds = case (length chds) of
  0 -> error "merge: Application with neither result nor argument?"
  1 -> let res = head chds
           r   = stmtRepr res
           i   = stmtUID  res
       in IntermediateStmt p i r
  2 -> let [res,arg] = chds
           r   = case stmtRepr arg of Right -> stmtRepr res; Wrong -> Right
           i   = stmtUID res
       in IntermediateStmt p i r
  _ -> error "merge: Application with multiple arguments?"

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
                       (nubMin $ foldr (\r as -> as ++ (arcsFrom r trace)) [] trace)
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

findFaulty' :: CompGraph -> [[CompStmt]]
findFaulty' = findFaulty wrongCC mergeCC

mergeCC ws = foldl (++) [] ws

wrongCC = foldl (\w r -> case stmtRepr r of Wrong -> True; _ -> w) False

debug :: Expr -> IO ()
debug redex = do
  let (reduct,compgraph) = tracedEval redex
  print (oldest $ findFaulty' compgraph)

debug' :: Expr -> IO ()
debug' redex = do
  let (reduct,compgraph) = tracedEval redex
  print (findFaulty' compgraph)

oldest :: [[CompStmt]] -> [[CompStmt]]
oldest [] = []
oldest rs = (:[]) . head . (sortWith getUID) $ rs
  where getUID = head . sort . (map stmtUID)

tracedEval :: Expr -> (Expr,CompGraph)
tracedEval = mkGraph . mkStmts . evaluate

disp :: Expr -> IO ()
disp expr = do 
  putStrLn (messages ++ strc)
  writeFile "log" (messages ++ strc)
  (display shw) . snd . mkGraph . mkStmts $ (reduct,trc)
  where (reduct,trc,messages) = evaluate' expr
        strc = foldl (\acc s -> acc ++ "\n" ++ s) "" (map show $ reverse trc)
        shw :: CompGraph -> String
        shw g = showWith g showVertex showArc
        showVertex = (foldl (++) "") . (map showCompStmt)
        showCompStmt rec = stmtLabel rec ++ " = " ++ show (stmtRepr rec) 
                         ++ " (with stack " ++ show (stmtStack rec) ++ ")\n"
        showArc (Arc _ _ dep)  = show dep

e1 = ACCFaulty "A" (Const Right)

e2 = Let ("x", Const Right) (ACCFaulty "X" (Var "x"))

e3 = Let ("i", (Const Right)) 
         (Apply (ACCFaulty "lam" (Lambda "x" (Var "x"))) "i")

e4 = Let ("i", (Const Right)) 
         (Apply (ACCFaulty "lam" (Lambda "x" (Const Right))) "i")


-- main = let i = Right
--            id = sacc "id" \y -> y
--        in (sacc "h" \f x -> f x) id i
--
e5 =  ACCCorrect "main"
      ( Let    ("i", (Const Right)) 
      ( Let    ("id",ACCFaulty "id" (Lambda "y" (Var "y")))
      {- in -} ( Apply 
                 ( Apply ( ACCCorrect "h" 
                   ( Lambda "f" (Lambda "x" (Apply (Var "f") "x"))
                   )
                 ) "id" ) "i"
               )
      )
      )

e5' = ( Let    ("i", (Const Right)) 
      ( Let    ("id",ACCFaulty "id" (Lambda "y" (Var "y")))
      {- in -} ( Apply 
                 ( Apply 
                   ( Lambda "f" (Lambda "x" (Apply (Var "f") "x"))
                   ) "id" ) "i"
               )
      )
      )

-- Demonstrates that it is important to consider 'call' as well when
-- adding dependencies based on the cost centre stack.
--
e6 = 
  ACCCorrect "Z"
  (Let 
    ("f",ACCCorrect "B" (Lambda "x" (ACCFaulty "L" (Const Right))))
    (Apply 
      (ACCCorrect "A" (Lambda "y" (Apply (Var "y") "z")))
    "f"
    )
  )


-- CC "Z" (let {f = CC "C" (\x . CC "L" 4), x = 5} (CC "A" f x))
e6' = (Let 
           ("f",ACCCorrect "L" (Lambda "x" (ACCFaulty "B" (Const Right))))
           (ACCCorrect "A" (Apply (Var "f") "y"))
      )

-- A demonstration of 'strange behaviour' because we don't properly
-- freshen our varibles: scopes don't work as we would expect them to.
-- In this case it results in two events that claim to be the arg-value of
-- the same parent-event.
e7 = Apply
      (Lambda "x"
        (Let
          ("z",Const Right)
          (Apply
            (Let
              ("y",Apply (Lambda "y" (ACCCorrect "D" (Lambda "z" (ACCFaulty "G" (Var "y"))))) "z")
              (Apply (Var "y") "y")
            )
            "x"
          )
        )
      ) "z"  -- Try replacing "z" with "a" here

-- An example of a tree with two branches that appear to be both faulty.
-- We can only guarantee the 'oldest' branch to be actually faulty.
e8 = ACCCorrect "root" (Let ("y",ACCFaulty "LET" (Const Right))
                            (ACCCorrect "IN" (Var "y"))
                       )


e9 = ACCCorrect "root" (Apply (Apply (Let ("x",Let ("y",Apply (Lambda "z" (ACCCorrect "CC1" (Lambda "y" (Var "z")))) "y") (Lambda "x" (ACCCorrect "CC2" (Var "x")))) (Apply (Let ("z",Apply (Lambda "z" (Var "y")) "z") (Apply (Apply (Var "x") "x") "z")) "y")) "x") "y")

e10 = ACCCorrect "root" (Apply (Apply (Let ("x",Lambda "y" (ACCFaulty "CC1" (Apply (Lambda "z" (ACCCorrect "CC2" (Var "z"))) "y"))) (Let ("y",Const Right) (Var "x"))) "x") "y")


-- Demonstrating the need for two levels of calls. Could this be necessary for n-levels? :(
-- See callDependency2.
-- But this only "works" because the let lives behind its scope...

e11 = ACCCorrect "root" 
        (Let   ("x",ACCCorrect "CC1" (Lambda "y" 
                  (ACCFaulty "CC2" (Apply (Lambda "x" (ACCCorrect "CC3" (Var "x"))) "y")))
               ) 
        {-in-} (Apply (Apply (Lambda "x" (ACCCorrect "CC4" (Apply (Lambda "y" (Lambda "x" (Apply (Apply (Var "x") "x") "z"))) "z"))) "y") "x"))

e12 = Let            ("f", ACCCorrect "f" $ Lambda "x" (Var "x"))
      $ Let          ("g", ACCCorrect "g" $ Lambda "y" (Apply (Var "f") "y"))
      $ Let          ("c", ACCCorrect "c" $ Const Right)
      $ {- in -}     ACCCorrect "main" (Apply (Var "g") "c")

      where cclet lbl b i = ACCCorrect lbl (Let b i)

e13 = Let        ("f", Lambda "y" (Var "y"))
      $ Let      ("f", Lambda "x" (Const Wrong))
      $ Let      ("c", Const Right)
      $ {- in -} Apply (Var "f") "c"

e14 = Let        ("id", ACCCorrect "id" $ Lambda "x" (Var "x"))
      $ Let      ("y", Const Right)
      $ Let      ("z", Apply (Var "id") "y")
      $ {- in -} (Apply (Var "id") "z")

e_id = Let ("id", ACCCorrect "id" (Lambda "x" (Var "x")))
     $ Let ("y", Const Right) $ Apply (Var "id") "y"

e_isort = Let ("insertC", Lambda "x" $ ACCCorrect "insert" (Var "x"))
        $ Let ("insertF", Lambda "x" $ ACCFaulty  "insert" (Var "x"))
        $ Let ("xs", Const Right)
        $ ACCCorrect "isort" $ Let ("ys", Apply (Var "insertC") "xs")
                             $ Apply (Var "insertF") "ys"

e_call = Let ("id", Lambda "x" $ ACCCorrect "id" (Var "x"))
       $ Let ("j", Const Right)
       $ ACCCorrect "root" (Apply (Var "id") "j")


-- let f x y = y in f 3
e_twoargs =  Let ("f", ACCCorrect "f" (Lambda "x" (Lambda "y" (Var "y"))))
          $  Let ("a", Const Right) 
          $  Let ("b", Const Right) 
          $ Apply (Apply (Var "f") "a") "b"



-- let h = \f -> f 3 in h id
e_ho = Let ("h", ACCCorrect "h" (Lambda "f" (Let ("c", Const Right)
                                             (Apply (Var "f") "c"))))
     $ Let ("id", Lambda "x" (Var "x"))
     $ Apply (Var "h") "id"


-- let {y = 3} (CC "A" (\x . (CC "B" x) 3))
e_nest = Let ("y", Const Right)
       $ ACCCorrect "A"
       $ Apply (Lambda "x" (ACCCorrect "B" (Var "x"))) "y"
