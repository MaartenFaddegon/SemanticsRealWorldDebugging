module TraceSemantics where

import Control.Monad.State
import Data.Graph.Libgraph

--------------------------------------------------------------------------------
-- Expressions

data Expr = ACC      Label Expr
          | Observed Label Stack Parent Expr
          | Const    Int
          | Lambda   Name Expr
          | Apply    Expr Name
          | Var      Name
          | Let      (Name,Expr) Expr
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
doLog msg = modify $ \cxt -> cxt{reduceLog = (msg ++ "\n") : reduceLog cxt}

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
        doLog (showd d ++ show n ++ ": " ++ show expr)
        reduct <- reduce expr
        modify $ \cxt -> cxt{depth=d}
        return reduct
  where showd 0 = ""
        showd n = '|' : showd (n-1)

--------------------------------------------------------------------------------
-- Manipulating the heap.

type Name = String
type Heap = [(Name,(Stack,Expr))]

insertHeap :: Name -> (Stack,Expr) -> State Context ()
insertHeap x e = modify $ \s -> s{heap = (x,e) : (heap s)}

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

setStack :: Stack -> State Context ()
setStack stk = modify $ \s -> s {stack = stk}

doPush :: Label -> State Context ()
doPush l = modify $ \s -> s {stack = push l (stack s)}

push :: Label -> Stack -> Stack
push l s
  | l `elem` s = dropWhile (/= l) s
  | otherwise  = l : s

doCall :: Stack -> State Context ()
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

reduce (ACC l e) = do
  stk <- gets stack
  doPush l
  eval reduce (Observed l stk Root e)

reduce (Observed l s p e) = do
  stk <- gets stack
  e' <- eval reduce e
  case e' of
    Exception msg ->
      return (Exception msg)
    (Const v) -> do
      uid <- getUniq
      doTrace (Record l s uid p (show v))
      return e'
    (Lambda x e) -> do
      uid <- getUniq
      let x' = "_1" ++ x; x'' = "_2" ++ x
          body = Let (x',Observed l stk (ArgOf uid) (Var x'')) 
                     (Apply (Lambda x (Observed l s (ResOf uid) e)) x')
      doTrace (Record l s uid p "\\")
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
subst n m (ACC l e)          = ACC l (subst n m e)
subst n m (Observed l s p e) = Observed l s p (subst n m e)

sub :: Name -> Name -> Name -> Name
sub n m n' = if n == n' then m else n'

--------------------------------------------------------------------------------
-- Tracing

type Trace = [Record]

data Record = Record
  { recordLabel  :: Label
  , recordStack  :: Stack
  , recordUID    :: UID
  , recordParent :: Parent
  , recordRepr   :: String
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
  doLog $ " * " ++ show rec
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


merge rec arg res =
  if lam && top
    then rec {recordRepr = recordLabel rec ++ " " ++ val arg ++ " = " ++ val res }
  else if lam
    then rec {recordRepr = "(\\" ++ val arg ++ " -> " ++ val res ++ ")"}
  else if top
    then rec {recordRepr = recordLabel rec ++ " = " ++ recordRepr rec}
    else rec
  where lam = recordRepr rec == "\\"
        top = recordParent rec == Root
        val Nothing = "_"
        val (Just r) = recordRepr r

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
                         :  map (callDependency src) trc
                         ++ map (flip callDependency src) trc
        couldDependOn  = yna couldDependOns

        -- The reverse of any
        yna :: [a->Bool] -> a -> Bool
        yna ps x = or (map (\p -> p x) ps)


nextStack :: Record -> Stack
nextStack rec = push (recordLabel rec) (recordStack rec)

pushDependency :: Record -> Record -> Bool
pushDependency p c = nextStack p == recordStack c

callDependency :: Record -> Record -> Record -> Bool
callDependency p q c = call (nextStack p) (nextStack q) == recordStack c

--------------------------------------------------------------------------------
-- Examples.

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
        showRecord = recordRepr
        showArc _  = ""

e1 = ACC "A" (Const 42)

e2 = Let ("x", Const 42) (ACC "X" (Var "x"))

e3 = Let ("i", (Const 42)) 
         (Apply (ACC "lam" (Lambda "x" (Var "x"))) "i")

e4 = Let ("i", (Const 42)) 
         (Apply (ACC "lam" (Lambda "x" (Const 1))) "i")

e5 =  ACC "main"
      ( Let ("i", (Const 42)) 
            ( Let ("id",ACC "id" (Lambda "y" (Var "y")))
                  ( Apply 
                    ( Apply 
                      ( ACC "h" 
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
  ACC "root"
  (Let 
    ("f",ACC "F1" (Lambda "x" (ACC "F2" (Const 1))))
    (Apply 
      (ACC "IN" (Lambda "y" (Apply (Var "y") "z")))
    "f"
    )
  )

-- A demonstration of 'strange behaviour' because we don't properly
-- freshen our varibles: scopes don't work as we would expect them to.
-- In this case it results in two records that claim to are the arg-value of
-- the same parent-record.
e7 = Apply
      (Lambda "x"
        (Let
          ("z",Const 42) 
          (Apply 
            (Let 
              ("y",Apply (Lambda "y" (ACC"D" (Lambda "z" (ACC"G" (Var "y"))))) "z")
              (Apply (Var "y") "y")
            )
            "x"
          )
        )
      ) "z"  -- Try replacing "z" with "a" here
