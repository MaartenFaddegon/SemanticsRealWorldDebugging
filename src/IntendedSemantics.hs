module IntendedSemantics where

import Control.Monad.State
import Prelude hiding (Right)
import Data.Graph.Libgraph
import Data.List (sort)
import GHC.Exts (sortWith)

--------------------------------------------------------------------------------
-- Expressions

data Expr = ACCCorrect Label Expr
          | ACCFaulty  Label Expr
          | Observed  Label Stack Parent Expr
          | Const     Judgement
          | Lambda    Name Expr
          | Apply     Expr Name
          | Var       Name
          | Let       (Name,Expr) Expr
          | Exception String
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
                       }

doLog :: String -> State Context ()
doLog msg = do
  d <- gets depth
  modify $ \cxt -> cxt{reduceLog = (showd d ++ msg ++ "\n") : reduceLog cxt}
  where showd 0 = " "
        showd n = '|' : showd (n-1)

evalWith' :: (Expr -> State Context Expr) -> Expr -> (Expr,Trace,String)
evalWith' reduce redex = (reduct,trace cxt,foldl (++) "" . reverse . reduceLog $ cxt)
  where (reduct,cxt) = runState (eval reduce redex) (Context [] 0 [] [] 0 1 [])

evalWith :: (Expr -> State Context Expr) -> Expr -> (Expr,Trace)
evalWith reduce redex = (reduct, trace cxt)
  where (reduct,cxt) = runState (eval reduce redex) (Context [] 0 [] [] 0 1 [])

eval :: (Expr -> State Context Expr) -> (Expr -> State Context Expr)
eval reduce expr = do 
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
insertHeap x e = do
  modify $ \s -> s{heap = (x,e) : (heap s)}
  doLog ("* added " ++ (show (x,e)) ++ " to heap")

deleteHeap :: Name -> State Context ()
deleteHeap x = modify $ \s -> s{heap = filter ((/= x) . fst) (heap s)}

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

stackIsNow = do
  stk <- gets stack
  doLog ("* Stack is now " ++ show stk)

setStack :: Stack -> State Context ()
setStack stk = do
  modify $ \s -> s {stack = stk}
  stackIsNow

doPush :: Label -> State Context ()
doPush l = do
  modify $ \s -> s {stack = push l (stack s)}
  stackIsNow

push :: Label -> Stack -> Stack
push l s
  | l `elem` s = dropWhile (/= l) s
  | otherwise  = l : s

doCall :: Stack -> State Context ()
doCall sLam = do
  modify $ \s -> s {stack = call (stack s) sLam}
  stackIsNow

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
  result <- reduce e2
  deleteHeap x
  return result

reduce (Apply f x) = do
  e <- eval reduce f
  case e of 
    (Lambda y e)  -> eval reduce (subst y x e)
    Exception msg -> return (Exception msg)
    _             -> return (Exception "Apply non-Lambda?")

reduce (Var x) = do
  r <- lookupHeap x
  case r of
    (_,Exception msg) -> do
      return (Exception msg)
    (stk,Const v) -> do
      setStack stk
      return (Const v)
    (stk,Lambda y e) -> do
      doCall stk
      return (Lambda y e)
    (stk,e) -> do
      deleteHeap x
      setStack stk
      v' <- eval reduce e
      case v' of
        Exception msg -> return (Exception msg)
        v -> do
          stkv <- gets stack
          insertHeap x (stkv,v)
          setStack stk
          eval reduce (Var x)

reduce (ACCCorrect l e) = do
  stk <- gets stack
  doPush l
  eval reduce (Observed l stk Root e)

reduce (ACCFaulty l e) = do
  stk <- gets stack
  doPush l
  uid <- getUniq
  doTrace (Record l stk uid Root Wrong)
  r <- eval reduce e
  case r of
    (Const jmt) -> return (Const Wrong)
    _           -> return r

reduce (Observed l s p e) = do
  stk <- gets stack
  e' <- eval reduce e
  case e' of
    Exception msg ->
      return (Exception msg)
    (Const v) -> do
      uid <- getUniq
      doTrace (Record l s uid p v)
      return e'
    (Lambda x e) -> do
      uid <- getUniq
      let x' = "_1" ++ x; x'' = "_2" ++ x
          body = Let (x',Observed l stk (ArgOf uid) (Var x'')) 
                     (Apply (Lambda x (Observed l s (ResOf uid) e)) x')
      doTrace (Record l s uid p Right)
      return (Lambda x'' body)
    e -> 
      return (Exception $ "Observe undefined: " ++ show e)

--------------------------------------------------------------------------------
-- Substituting variable names.

subst :: Name -> Name -> Expr -> Expr
subst n m (Const v)          = Const v
subst n m (Lambda n' e)      = Lambda (sub n m n') (subst n m e)
subst n m (Apply e n')       = Apply (subst n m e) (sub n m n')
subst n m (Var n')           = Var (sub n m n')
subst n m (Let (n',e1) e2)   = Let ((sub n m n'),(subst n m e1)) (subst n m e2)
subst n m (ACCCorrect l e)   = ACCCorrect l (subst n m e)
subst n m (ACCFaulty l e)    = ACCFaulty l (subst n m e)
subst n m (Observed l s p e) = Observed l s p (subst n m e)

sub :: Name -> Name -> Name -> Name
sub n m n' = if n == n' then m else n'

--------------------------------------------------------------------------------
-- Tracing

data Judgement  = Right | Wrong deriving (Show,Eq,Ord)

type Trace = [Record]

data Record = Record
  { recordLabel  :: Label
  , recordStack  :: Stack
  , recordUID    :: UID
  , recordParent :: Parent
  , recordRepr   :: Judgement
  } deriving (Show,Eq,Ord)

type UID = Int

data Parent = Root | ArgOf UID | ResOf UID deriving (Show,Eq,Ord)

getUniq :: State Context UID
getUniq = do
  i <- gets uniq
  modify $ \cxt -> cxt { uniq = i + 1 }
  return i

doTrace :: Record -> State Context ()
doTrace rec = do
  doLog $ "* " ++ show rec
  modify $ \cxt -> cxt{trace = rec : trace cxt}

-- MF TODO: in some weird cases it seems to happen that there are multiple children.
-- I now just pick the first put that may not be what we really want. This
-- may be related to our not so sophisticated scope rules (should we implement
-- freshen?).
successors :: Trace 
           -> (Record -> Maybe (Record ) -> Maybe Record -> Record)
           -> Record -> Record
successors trc merge rec = merge rec arg res
  where arg = suc ArgOf
        res = suc ResOf
        suc con = case filter (\chd -> recordParent chd == con (recordUID rec)) trc of
          []    -> Nothing
          chd:_ -> Just (successors trc merge chd)

--------------------------------------------------------------------------------
-- Trace post processing

mkEquations :: (Expr,Trace) -> (Expr,Trace)
mkEquations (reduct,trc) = (reduct,filter isRoot . map (successors trc merge) $ trc)
  where isRoot = (== Root) . recordParent

merge :: Record -> Maybe Record -> Maybe Record -> Record
merge rec arg res = rec{ recordRepr=(recordRepr rec) `or` (jmt arg) `or` (jmt res)
                       , recordUID=newest [recordUID rec, getUID arg, getUID res]
                       }
  where jmt mr = case mr of Just r -> recordRepr r; Nothing -> Right
        or Wrong _ = Wrong
        or _ Wrong = Wrong
        or _ _     = Right
        newest = last . sort
        getUID Nothing = 0
        getUID (Just r) = recordUID r

--------------------------------------------------------------------------------
-- Debug

type CompGraph = Graph [Record]

mkGraph :: (Expr,Trace) -> (Expr,CompGraph)
mkGraph (reduct,trc) = (reduct,mapGraph (\r->[r]) (mkGraph' trc))

mkGraph' :: Trace -> Graph (Record)
mkGraph' trace = Graph (head roots)
                       trace
                       (foldr (\r as -> as ++ (arcsFrom r trace)) [] trace)
  where roots = filter (\rec -> recordStack rec == []) trace

arcsFrom :: Record -> Trace -> [Arc Record]
arcsFrom src trc = (map (Arc src)) . (filter couldDependOn) $ trc
  where couldDependOns = pushDependency src 

                         -- function-as-parent
                         : map (flip callDependency src) trc

                         -- application-as-parent
                         -- : map (callDependency src) trc
                        
                         -- neither
                         -- : []


        couldDependOn  = yna couldDependOns

        -- The reverse of any
        yna :: [a->Bool] -> a -> Bool
        yna ps x = or (map (\p -> p x) ps)


nextStack :: Record -> Stack
nextStack rec = push (recordLabel rec) (recordStack rec)

pushDependency :: Record -> Record -> Bool
pushDependency p c = nextStack p == recordStack c

callDependency :: Record -> Record -> Record -> Bool
callDependency pApp pLam c = call (nextStack pApp) (nextStack pLam) == recordStack c

--------------------------------------------------------------------------------
-- Examples.

findFaulty' :: CompGraph -> [[Record]]
findFaulty' = findFaulty wrongCC mergeCC
  where mergeCC ws = foldl (++) [] ws
        wrongCC = foldl (\w r -> case recordRepr r of Wrong -> True; _ -> w) False

debug :: Expr -> IO ()
debug redex = do
  let (reduct,compgraph) = tracedEval redex
  print (oldest $ findFaulty' compgraph)

debug' :: Expr -> IO ()
debug' redex = do
  let (reduct,compgraph) = tracedEval redex
  print (findFaulty' compgraph)


oldest :: [[Record]] -> [[Record]]
oldest [] = []
oldest rs = (:[]) . head . (sortWith getUID) $ rs
  where getUID = head . sort . (map recordUID)

tracedEval :: Expr -> (Expr,CompGraph)
tracedEval = mkGraph . mkEquations . (evalWith reduce)

disp :: Expr -> IO ()
disp expr = do 
  putStr messages
  (display shw) . snd . mkGraph . mkEquations $ (reduct,trc)
  where (reduct,trc,messages) = evalWith' reduce expr
        shw :: CompGraph -> String
        shw g = showWith g showVertex showArc
        showVertex = (foldl (++) "") . (map showRecord)
        showRecord rec = recordLabel rec ++ " = " ++ show (recordRepr rec) 
                         ++ " (with stack " ++ show (recordStack rec) ++ ")\n"
        showArc _  = ""

e1 = ACCFaulty "A" (Const Right)

e2 = Let ("x", Const Right) (ACCFaulty "X" (Var "x"))

e3 = Let ("i", (Const Right)) 
         (Apply (ACCFaulty "lam" (Lambda "x" (Var "x"))) "i")

e4 = Let ("i", (Const Right)) 
         (Apply (ACCFaulty "lam" (Lambda "x" (Const Right))) "i")

e5 =  ACCCorrect "main"
      ( Let ("i", (Const Right)) 
            ( Let ("id",ACCFaulty "id" (Lambda "y" (Var "y")))
                  ( Apply 
                    ( Apply 
                      ( ACCCorrect "h" 
                        ( Lambda "f" 
                          ( Lambda "x"
                            ( Apply (Var "f") "x"
                            )
                          )
                        )
                      ) "id"
                    ) "i"
                  )
            )
      )

-- Demonstrates that it is important to consider 'call' as well when
-- adding dependencies based on the cost centre stack.
e6 = 
  ACCCorrect "root"
  (Let 
    ("f",ACCCorrect "F1" (Lambda "x" (ACCFaulty "F2" (Const Right))))
    (Apply 
      (ACCCorrect "IN" (Lambda "y" (Apply (Var "y") "z")))
    "f"
    )
  )

-- A demonstration of 'strange behaviour' because we don't properly
-- freshen our varibles: scopes don't work as we would expect them to.
-- In this case it results in two records that claim to be the arg-value of
-- the same parent-record.
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
