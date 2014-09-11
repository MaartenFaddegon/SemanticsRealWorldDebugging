module IntendedSemantics where

import Control.Monad.State
import Prelude hiding (Right)
import Data.Graph.Libgraph
import Data.List (sort)
import GHC.Exts (sortWith)
import Data.List (partition)
import Data.Algorithm.Diff

--------------------------------------------------------------------------------
-- Expressions

data Expr = ACCCorrect Label Expr
          | ACCFaulty  Label Expr
          | Observed   Parent Expr
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
                       , freshVarNames  :: ![Name]
                       }

doLog :: String -> State Context ()
doLog msg = do
  d <- gets depth
  modify $ \cxt -> cxt{reduceLog = (showd d ++ msg ++ "\n") : reduceLog cxt}
  where showd 0 = " "
        showd n = '|' : showd (n-1)

evalWith' :: Expr -> (Expr,Trace,String)
evalWith' redex = (reduct,trace cxt,foldl (++) "" . reverse . reduceLog $ cxt)
  where (reduct,cxt) = runState (eval redex) state0

evalWith :: Expr -> (Expr,Trace)
evalWith redex = (reduct, trace cxt)
  where (reduct,cxt) = runState (eval redex) state0

state0 = Context [] 0 [] [] 0 1 [] (map (("fresh"++) . show) [1..])

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
        -- doLog (show n ++ ": " ++ show reduct)
        -- doLog (show n ++ "  " ++ diffshow expr reduct)
        modify $ \cxt -> cxt{depth=d}
        return reduct

  where diffshow :: Expr -> Expr -> String
        diffshow expr reduct = let shw (First _)  = '-'
                                   shw (Second _) = '+'
                                   shw (Both _ _) = ' '
                               in map shw $ getDiff (show expr) (show reduct)

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
  -- before <- lookupHeap x

  stk <- gets stack
  insertHeap x (stk,e1)
  eval e2

  -- reduct <- eval e2
  -- doLog $ "Delete " ++ x ++ " from heap."
  -- deleteHeap x
  -- insertHeap x before
  -- return reduct

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
  doTrace (Enter l stk uid)
  eval (Observed (Parent uid) e)

reduce (ACCFaulty l e) = do
  stk <- gets stack
  doPush l
  uid <- getUniq; uidc <- getUniq
  doTrace (Enter l stk uid); doTrace (ConstRecord uidc (Parent uid) Wrong)
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
    (Const v) -> do
      uid <- getUniq
      doTrace (ConstRecord uid p v)
      return e'
    (Lambda x e) -> do
      uid <- getUniq
      x1 <- getFreshVar
      x2 <- getFreshVar
      let body = Let    (x1,Observed (ArgOf uid) (Var x2)) 
                 {-in-} (Apply (Lambda x (Observed (ResOf uid) e)) x1)
      doTrace (LamRecord uid p)
      return (Lambda x2 body)
    e -> 
      return (Exception $ "Observe undefined: " ++ show e)

reduce (Exception msg) = return (Exception msg)

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
subst n m (Observed p e)     = Observed p (subst n m e)

sub :: Name -> Name -> Name -> Name
sub n m n' = if n == n' then m else n'

--------------------------------------------------------------------------------
-- Fresh variable names

fresh :: Expr -> State Context Expr

fresh (Const v) = do
  return (Const v)

fresh (Lambda x e) = do 
  y <- getFreshVar
  e' <- (fresh . subst x y) e
  return (Lambda y e')

fresh (Let (x,e1) e2) = do 
  y <- getFreshVar
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

fresh (Exception msg) = return (Exception msg)

getFreshVar :: State Context Name
getFreshVar = do
  (x:xs) <- gets freshVarNames
  modify $ \cxt -> cxt {freshVarNames=xs}
  return x

--------------------------------------------------------------------------------
-- Tracing

data Judgement  = Right | Wrong deriving (Show,Eq,Ord)

type Trace = [Record]

data Record
  = Enter
    { recordLabel  :: Label
    , recordStack  :: Stack
    , recordUID    :: UID
    } 
  | ConstRecord
    { recordUID    :: UID
    , recordParent :: Parent
    , recordRepr   :: Judgement
    }
  | LamRecord
    { recordUID    :: UID
    , recordParent :: Parent
    }
  deriving (Show,Eq,Ord)

data Equation
 = FinalEquation
    { equationLabel  :: Label
    , equationStack  :: Stack
    , equationUID    :: UID
    , equationRepr   :: Judgement
    }
 | IntermediateEquation
    { equationParent :: Parent
    , equationUID    :: UID
    , equationRepr   :: Judgement
    }
  deriving (Show,Eq,Ord)

type UID = Int

data Parent = Parent UID | ArgOf UID | ResOf UID deriving (Show,Eq,Ord)

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
           -> (Record -> Maybe Equation -> Maybe Equation -> Equation)
           -> Record -> Equation
successors trc merge rec = case rec of
        (LamRecord _ _) -> merge rec (suc ArgOf) (suc ResOf)
        (Enter _ _ _)   -> merge rec (suc Parent) Nothing

  where suc con = case filter (\chd -> recordParent chd == con (recordUID rec)) trc of
          []                         -> Nothing
          (ConstRecord uid p repr):_ -> Just (IntermediateEquation p uid repr)
          chd:_                      -> Just (successors trc merge chd)

recP (Enter _ _ _) = error "Oeps, enter a child?"
recP r             = recordParent r

--------------------------------------------------------------------------------
-- Trace post processing

mkEquations :: (Expr,Trace) -> (Expr,[Equation])
mkEquations (reduct,trc) = (reduct,map (successors chds merge) roots)
  where isRoot (Enter _ _ _) = True
        isRoot _             = False
        (roots,chds) = partition isRoot trc

jmt :: Maybe Equation -> Judgement
jmt (Just e) = equationRepr e
jmt Nothing  = Right

merge :: Record -> Maybe Equation -> Maybe Equation -> Equation
merge (Enter lbl stk uid) chd _
  = FinalEquation lbl stk uid (jmt chd)

merge (LamRecord uid p) arg res
  = IntermediateEquation p
        (newest [uid, getUID arg, getUID res])
        ((jmt res) `argOr` (jmt arg))

    where 
      or Wrong _ = Wrong
      or _ Wrong = Wrong
      or _ _     = Right
      
      argOr _ Wrong = Right
      argOr Wrong _ = Wrong
      argOr _ _     = Right
      
      newest = last . sort

      getUID Nothing = 0
      getUID (Just r) = equationUID r
                                
{-
merge rec arg res = ConstRecord (newest [recordUID rec, getUID arg, getUID res])
                                (recordParent rec)
                                ((recordRepr rec) `or` (jmt res) `argOr` (jmt arg))
-}


--------------------------------------------------------------------------------
-- Debug

data Dependency = PushDep | CallDep Int deriving (Eq,Show)

instance Ord Dependency where
  compare PushDep (CallDep _)     = LT
  compare (CallDep _) PushDep     = GT
  compare (CallDep n) (CallDep m) = compare n m
  compare PushDep PushDep         = EQ

type CompGraph = Graph [Equation] Dependency

mkGraph :: (Expr,[Equation]) -> (Expr,CompGraph)
mkGraph (reduct,trc) = (reduct,mapGraph (\r->[r]) (mkGraph' trc))

mkGraph' :: [Equation] -> Graph Equation Dependency
mkGraph' trace
  | length trace < 1 = error "mkGraph: empty trace"
  | length roots < 1 = error "mkGraph: no root"
  | otherwise = Graph (head roots)
                       trace
                       (nubMin $ foldr (\r as -> as ++ (arcsFrom r trace)) [] trace)
  where roots = filter isRoot trace
        isRoot FinalEquation{equationStack=s} = s == []
        isRoot _                              = error "mkGraph': Leftover intermediate equation?"

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

arcsFrom :: Equation -> [Equation] -> [Arc Equation Dependency]
arcsFrom src trc =  ((map (\tgt -> Arc src tgt PushDep)) . (filter isPushArc) $ trc)
                 ++ ((map (\tgt -> Arc src tgt (CallDep 1))) . (filter isCall1Arc) $ trc)
                 -- MF TODO: do we need level-2 arcs?
                 -- ++ ((map (\tgt -> Arc src tgt (CallDep 2))) . (filter isCall2Arc) $ trc)
                 

  where isPushArc = pushDependency src
        
        isCall1Arc = -- function-as-parent
                    anyOf $ map (flip callDependency src) trc
                    -- application-as-parent
                    -- anyOf $ map (callDependency src) trc

        isCall2Arc = anyOf $  apmap (map (callDependency2 src) trc) trc
                           ++ apmap (map (callDependency2' src) trc) trc

        anyOf :: [a->Bool] -> a -> Bool
        anyOf ps x = or (map (\p -> p x) ps)

        apmap :: [a->b] -> [a] -> [b]
        apmap fs xs = foldl (\acc f -> acc ++ (map f xs)) [] fs

nextStack :: Equation -> Stack
nextStack rec = push (equationLabel rec) (equationStack rec)

pushDependency :: Equation -> Equation -> Bool
pushDependency p c = nextStack p == equationStack c

callDependency :: Equation -> Equation -> Equation -> Bool
callDependency pApp pLam c = call (nextStack pApp) (nextStack pLam) == equationStack c


callDependency2 :: Equation -> Equation -> Equation -> Equation -> Bool
callDependency2 pApp pApp' pLam' c = call (nextStack pApp) pLam == equationStack c
  where pLam = call (nextStack pApp') (nextStack pLam')

callDependency2' :: Equation -> Equation -> Equation -> Equation -> Bool
callDependency2' pApp1 pApp2 pLam c = call pApp (nextStack pLam) == equationStack c
  where pApp = call (nextStack pApp1) (nextStack pApp2)


--------------------------------------------------------------------------------
-- Examples.

findFaulty' :: CompGraph -> [[Equation]]
findFaulty' = findFaulty wrongCC mergeCC

mergeCC ws = foldl (++) [] ws

wrongCC = foldl (\w r -> case equationRepr r of Wrong -> True; _ -> w) False

debug :: Expr -> IO ()
debug redex = do
  let (reduct,compgraph) = tracedEval redex
  print (oldest $ findFaulty' compgraph)

debug' :: Expr -> IO ()
debug' redex = do
  let (reduct,compgraph) = tracedEval redex
  print (findFaulty' compgraph)

oldest :: [[Equation]] -> [[Equation]]
oldest [] = []
oldest rs = (:[]) . head . (sortWith getUID) $ rs
  where getUID = head . sort . (map equationUID)

tracedEval :: Expr -> (Expr,CompGraph)
tracedEval = mkGraph . mkEquations . evalWith

disp :: Expr -> IO ()
disp expr = do 
  putStrLn (show reduct)
  -- writeFile "log" $ messages 
  putStrLn $ messages 
        ++ "\ntrace: " ++ show trc
        ++ "\nequations: " ++ show (snd . mkEquations $ (reduct,trc))
        ++ "\nreduct: " ++ (show reduct)
  (display shw) 
               -- (collapse mergeCC) 
               -- . remove 
               . snd . mkGraph . mkEquations $ (reduct,trc)
  where (reduct,trc,messages) = evalWith' expr
        shw :: CompGraph -> String
        shw g = showWith g showVertex showArc
        showVertex = (foldl (++) "") . (map showEquation)
        showEquation rec = equationLabel rec ++ " = " ++ show (equationRepr rec) 
                         ++ " (with stack " ++ show (equationStack rec) ++ ")\n"
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

-- e12 = cclet "let1"        ("ap1", ap)
--         (cclet "let2"     ("ap2", ap)
--           (cclet "let3"   ("f", ACCCorrect "f" (Lambda "i" (Var "i")))
--             (cclet "let4" ("x", ACCFaulty "x" (Const Right))
--               (ACCCorrect "main"
--                 $ Apply (Apply (Apply (Var "ap1") "ap2") "f") "x"
--               )
--             )
--           )
--         )
-- 
--         where cclet lbl b i = ACCCorrect lbl (Let b i)
--               ap = Lambda "fun" (Lambda "arg" (Apply (Var "fun") "arg"))
