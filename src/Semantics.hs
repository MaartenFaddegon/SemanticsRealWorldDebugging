import Control.Monad.State
import Prelude hiding (Right)
import Test.QuickCheck
import Data.Graph.Libgraph

import qualified Debug.Trace as Debug

--------------------------------------------------------------------------------
-- Stack handling: push and call

type Label = String
type Stack = [Label]

push :: Label -> Stack -> Stack
push l s
  | l `elem` s = dropWhile (/= l) s
  | otherwise  = l : s

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
-- Expressions.

type Name = String

data Expr = Const
          | Lambda Name Expr
          | Apply  Expr Name
          | Var    Name
          | Let    (Name,Expr) Expr
          | ACCCorrect Label Expr
          | ACCFaulty  Label Expr
          | Observed   Label Stack Expr
          | Exception  String

          deriving (Show,Eq)

--------------------------------------------------------------------------------
-- The reduction rules.

eval :: Stack -> Trace -> Expr -> E (Stack,Trace,Expr)

eval stk trc Const = return (stk,trc,Const)

eval stk trc (Lambda x e) = return (stk,trc,Lambda x e)

eval stk trc (ACCCorrect l e) = evalUpto (push l stk) trc (Observed l stk e)

eval stk trc (ACCFaulty l e)  = evalUpto (push l stk) (trace (l,stk,Wrong) trc) e

eval stk trc (Let (x,e1) e2) = do
  insertHeap x (stk,e2)
  eval stk trc e2

-- We added a special case for weird testcases that try to apply non-Lambda
-- expressions. And we break out of endless loops by returning a Const when we
-- detect such a loop.
eval stk trc orig@(Apply f x) = do
  (stk_lam, trc_lam, e) <- evalUpto stk trc f
  case e of 
    Lambda y e -> evalUpto stk_lam trc_lam (subst y x e)
    _          -> return (stk_lam,trc_lam,Exception "Apply non-Lambda?")

eval stk trc (Var x) = do
  r <- lookupHeap x
  case r of
    (stk',Const)  -> return (stk',trc,Const)
    (stk',Lambda y e) -> return (call stk stk',trc,Lambda y e)
    (stk',e) -> do
      deleteHeap x
      (stkv,trcv,v) <- evalUpto stk' trc e
      insertHeap x (stkv,v)
      evalUpto stk trcv (Var x) -- Notice how we retain the trace but swap back the stack

-- MF TODO: Ik denk dat alle gevallen hier behandeld moeten worden ipv de _ op het eind?
eval stk trc (Observed l s e) = do
  case e of Const              -> return (stk,trace (l,s,Right) trc, Const)
            (ACCFaulty l' e')  -> evalUpto stk (trace (l,s,Wrong) trc) (ACCFaulty l' e')
            (ACCCorrect l' e') -> evalUpto stk trc (ACCCorrect l' (Observed l s e'))
            (Let (x,e1) e2)    -> evalUpto stk trc (Let (x,e1) (Observed l s e2))
            _ -> do
              (stk',trc',e') <- evalUpto stk trc e
              evalUpto stk' trc' (Observed l s e')


eval stk trc (Exception s) = return (stk,trc,Exception s)


evalUpto :: Stack -> Trace -> Expr -> E (Stack,Trace,Expr)
evalUpto stk trc expr = do n <- gets steps
                           -- let n = Debug.trace (  "step" ++ show n' ++ ": " ++ show expr ++ "\n"
                           --                     ++ "  with trace " ++ show trc
                           --                     ) 
                           --                     n'
                           modify $ \s -> s {steps = n+1}
                           if n > 500
                             then return (stk,trc,Exception "Too many steps!")
                             else eval stk trc expr

--------------------------------------------------------------------------------
-- The state.

data EState = EState { theHeap      :: ![(Name,(Stack,Expr))]
                     , steps        :: !Int
                     }

type E a = State EState a

evalE' :: Expr -> (Stack,Trace,Expr)
evalE' e = evalState (evalUpto [] [] e) (EState [] 0)

evalE :: Expr -> Trace
evalE e = let (_,t,_) = evalE' e in t

--------------------------------------------------------------------------------
-- Manipulating the heap

insertHeap :: Name -> (Stack,Expr) -> E ()
insertHeap x e = modify $ \s -> s{theHeap = (x,e) : (theHeap s)}

deleteHeap :: Name -> E ()
deleteHeap x = modify $ \s -> s{theHeap = filter ((/= x) . fst) (theHeap s)}

lookupHeap :: Name -> E (Stack,Expr)
lookupHeap x = do 
  me <- fmap (lookup x . theHeap) get
  case me of
    Nothing -> return ([], Const) -- Keep going with a Const if we find nothing.
    Just e  -> return e

--------------------------------------------------------------------------------
-- Substituting variable names.

subst :: Name -> Name -> Expr -> Expr
subst n m Const             = Const
subst n m (Lambda n' e)     = Lambda (sub n m n') (subst n m e)
subst n m (Apply e n')      = Apply (subst n m e) (sub n m n')
subst n m (Var n')          = Var (sub n m n')
subst n m (Let (n',e1) e2)  = Let ((sub n m n'),(subst n m e1)) (subst n m e2)
subst n m (ACCCorrect l e) = ACCCorrect l (subst n m e)
subst n m (ACCFaulty l e)  = ACCFaulty l (subst n m e)

sub :: Name -> Name -> Name -> Name
sub n m n' = if n == n' then n' else m

--------------------------------------------------------------------------------
-- Tracing.
--
-- A recorded value is Right or Wrong.

data Value  = Right | Wrong       deriving (Show,Eq,Ord)
type Record = (Label,Stack,Value)
type Trace  = [Record]

trace :: Record -> Trace -> Trace
trace = (:)

--------------------------------------------------------------------------------
-- Algorithmic debugging from a trace.

faultyNodes :: Expr -> [Label]
faultyNodes = getLabels . (findFaulty wrongCC mergeCC) . mkGraph . evalE 

wrongCC :: Vertex -> Bool
wrongCC (Vertex rs) = foldl (\w r -> case r of (_,_,Wrong) -> True; _ -> w) False rs

getLabels = foldl accLabels []
  where accLabels acc v = acc ++ getLabels' v
        getLabels' (Vertex rs) = map (\(l,_,_) -> l) rs

data Vertex = Vertex [Record] deriving (Eq,Ord)

mkGraph :: Trace -> Graph Vertex
mkGraph trace = mapGraph (\r -> Vertex [r]) (mkGraph' trace)

mkGraph' :: Trace -> Graph Record
mkGraph' trace = Graph (last trace)
                       trace
                       (foldr (\r as -> as ++ (arcsFrom r trace)) [] trace)

arcsFrom :: Record -> Trace -> [Arc Record]
arcsFrom src = (map (Arc src)) . (filter (src `couldDependOn`))

couldDependOn :: Record -> Record -> Bool
couldDependOn (l,s,_) (_,t,_) = push l s == t

-- algoDebug :: Graph Vertex -> [Label]
-- algoDebug g@(Graph _ vs as) = foldl accLabels [] (filter faulty vs)
--         where accLabels acc v = acc ++ getLabels v
--               faulty :: Vertex -> Bool
--               faulty v = isWrong v && (null $ (filter isWrong) (succs g v))


-- getLabels :: Vertex -> [Label]
-- getLabels (Vertex rs) = map (\(l,_,_) -> l) rs


--------------------------------------------------------------------------------
-- Removing cycles from a graph.

-- rmCycles :: Graph Vertex -> Graph Vertex
-- rmCycles g = dagify merge g

mergeCC :: [Vertex] -> Vertex
mergeCC ws = foldl merge' (Vertex []) ws
  where merge' (Vertex qs) (Vertex rs) = Vertex (qs ++ rs)

--------------------------------------------------------------------------------
-- List of faulty expressions (static analysis).

faultyExprs :: Expr -> [Label]
faultyExprs Const             = []
faultyExprs (Lambda _ e)      = faultyExprs e
faultyExprs (Apply e _)       = faultyExprs e
faultyExprs (Var _)           = []
faultyExprs (Let (_,e1) e2)   = faultyExprs e1 ++ faultyExprs e2
faultyExprs (ACCCorrect _ e)  = faultyExprs e
faultyExprs (ACCFaulty l e)   = l : faultyExprs e

--------------------------------------------------------------------------------
-- Tests.

gen_expr :: Int -> Gen Expr
gen_expr 0 = elements [Const]
gen_expr n = oneof [ elements [Const]
                   , liftM2 Lambda      gen_name gen_expr'
                   , liftM2 Apply       gen_expr' gen_name
                   , liftM  Var         gen_name
                   , liftM3 mkLet       gen_name gen_expr' gen_expr'
                   , liftM2 ACCCorrect gen_label gen_expr'
                   , liftM2 ACCFaulty  gen_label gen_expr'
                   ]
  where gen_expr' = gen_expr (n-1)
        mkLet n e1 e2 = Let (n,e1) e2
        gen_label = elements $ map (:[]) ['A'..'Z']
        gen_name  = elements $ map (:[]) ['x'..'z']

instance Arbitrary Expr where
  arbitrary = sized gen_expr

propValidExpr :: Expr -> Bool
propValidExpr e = let (_,_,e') = evalE' e in e' == Const

propExact :: Expr -> Bool
propExact e = faultyNodes e == faultyExprs e

propSubset :: Expr -> Bool
propSubset e = (faultyNodes e) `subset` (faultyExprs e)

subset :: Eq a => [a] -> [a] -> Bool
subset xs ys = foldr ((&&) . (`elem` ys)) True xs

propFoundFaulty :: Expr -> Bool
propFoundFaulty e = faultyNodes e /= []

propIsWrong :: Expr -> Bool
propIsWrong e = case lookupT "toplevel" (evalE $ Observed "toplevel" [] e) of
  (Just Wrong) -> True
  _            -> False

lookupT :: Label -> Trace -> Maybe Value
lookupT l t = lookup l (zip ls vs)
  where (ls,_,vs) = unzip3 t

propFaultyIfWrong e = propIsWrong e ==> propFoundFaulty e

main = quickCheckWith args (\e -> propValidExpr e ==> propFaultyIfWrong e)
  where args = Args { replay          = Nothing
                    , maxSuccess      = 100000  -- number of tests
                    , maxDiscardRatio = 10
                    , maxSize         = 1000    -- max subexpressions
                    , chatty          = True
                    }

---

showGraph :: Graph Vertex -> String
showGraph g = showWith g showVertex noShow 

showVertex :: Vertex -> String
showVertex (Vertex rs) = show rs

noShow :: Arc a -> String
noShow _ = ""

---

expr1 = ACCCorrect "y" (ACCFaulty "x" Const)
expr2 = Let ("e",ACCFaulty "K" Const) (Let ("d",Const) Const)
expr3 = Let ("n",Lambda "n" Const) (Var "n")
expr4 = Let ("n", Const) (Var "n")

test1 = propExact expr1

-- Doesn't terminate:
test2  = evalE $ Apply (Lambda "y" (Apply (                 (Lambda "z" ((Apply (Var "y") "z")))) "z")) "z"

test2b = evalE $ Apply (Lambda "y" (Apply (Let ("x",Const) (Lambda "z" ((Apply (Var "y") "z")))) "z")) "z"


test2c = evalE $ Apply ((Apply (Let ("z",Apply Const "x") (Lambda "z" (Apply ((Apply ((Apply (Var "x") "x")) "y")) "y"))) "z")) "z"

test2d = evalE $ Apply (ACCCorrect "E" (Apply (Let ("z",Apply Const "x") (Lambda "z" (Apply (ACCCorrect "O" (Apply (ACCCorrect "D" (Apply (Var "x") "x")) "y")) "y"))) "z")) "z"

-- lookup failed?

test3a = faultyNodes $ ACCFaulty "A" (ACCCorrect "B" Const)
test3b = (display showGraph) . mkGraph . evalE $ ACCFaulty "A" (ACCCorrect "B" Const)
-- test3c = (display showGraph) . rmCycles . mkGraph . evalE $ ACCFaulty "L" (ACCFaulty "L" (Var "z"))

e4 = ACCFaulty "O" (ACCCorrect "C" (Let ("y",Const) (ACCCorrect "R" (ACCCorrect "F" (Var "y")))))

test4a = (display showGraph) . mkGraph . evalE $ e4

test4b = evalE e4

e5 = ACCFaulty "OUTER" (ACCCorrect "INNER" (Let ("x",Const) (Var "x")))

e6 = ACCFaulty "A" (ACCCorrect "B" (ACCCorrect "C" (ACCFaulty "D" (Var "x"))))

test = (display showGraph) . (dagify mergeCC) . mkGraph . evalE
test' = (display showGraph) . mkGraph . evalE

e7 = ACCFaulty "A" (ACCCorrect "B" (Apply (ACCFaulty "C" (Apply (Let ("z",Apply (Apply (Var "y") "x") "x") (Lambda "z" (ACCFaulty "D" (ACCFaulty "E" (Var "x"))))) "z")) "y"))

e7' = ACCFaulty "A" 
        (ACCCorrect "B"
          (Apply 
            (Apply 
              (Let
                ("z", Const )
                (Lambda "z" 
                  (ACCFaulty "C" (ACCFaulty "D" (Var "x")))
                )
              ) 
            "z"
            ) 
           "y"
          )
        )

-- e7' = ACCFaulty "A" (ACCCorrect "B" (Apply ((Apply (Let ("z",Apply (Apply (Var "y") "x") "x") (Lambda "z" (ACCFaulty "D" (ACCFaulty "E" (Var "x"))))) "z")) "y"))
