import Control.Monad.State
import Prelude hiding (Right)
import Test.QuickCheck
import Data.Graph.Libgraph
import Runtime
import qualified Debug.Trace as Debug

--------------------------------------------------------------------------------
-- Expressions.

data Expr = Const
          | Lambda Name Expr
          | Apply  Expr Name
          | Var    Name
          | Let    (Name,Expr) Expr
          | ACCCorrect Label Expr
          | ACCFaulty  Label Expr
          | Observed   Label Stack Expr
          deriving (Show,Eq)

--------------------------------------------------------------------------------
-- The reduction rules.

eval :: Stack -> Trace -> Expr -> State (Context Expr) (Stack,Trace,ExprExc Expr)

eval stk trc Const = 
  return (stk,trc,Expression Const)

eval stk trc (Lambda x e) = 
  return (stk,trc,Expression $ Lambda x e)

eval stk trc (ACCCorrect l e) =
  evalUpto eval (push l stk) trc (Observed l stk e)

eval stk trc (ACCFaulty l e)  =
  evalUpto eval (push l stk) (trace (l,stk,Wrong) trc) e

eval stk trc (Let (x,e1) e2) = do
  insertHeap x (stk,e2)
  eval stk trc e2

-- We added a special case for weird testcases that try to apply non-Lambda
-- expressions. And we break out of endless loops by returning a Const when we
-- detect such a loop.
eval stk trc orig@(Apply f x) = do
  (stk_lam, trc_lam, e) <- evalUpto eval stk trc f
  case e of 
    Expression (Lambda y e) -> evalUpto eval stk_lam trc_lam (subst y x e)
    Exception msg           -> return (stk_lam,trc_lam,Exception msg)
    _                       -> return (stk_lam,trc_lam,Exception "Apply non-Lambda?")

eval stk trc (Var x) = do
  r <- lookupHeap x
  case r of
    (stk',Exception msg)           -> return (stk',trc,Exception msg)
    (stk',Expression Const)        -> return (stk',trc,Expression Const)
    (stk',Expression (Lambda y e)) -> return (call stk stk',trc,Expression (Lambda y e))
    (stk',Expression e) -> do
      deleteHeap x
      (stkv,trcv,v') <- evalUpto eval stk' trc e
      case v' of
        Exception msg -> return (stkv,trcv,Exception msg)
        Expression v  -> do
          insertHeap x (stkv,v)
          evalUpto eval stk trcv (Var x) -- Notice how we retain the trace but swap back the stack

-- MF TODO: Ik denk dat alle gevallen hier behandeld moeten worden ipv de _ op het eind?
eval stk trc (Observed l s e) = do
  case e of Const              -> return (stk,trace (l,s,Right) trc,Expression Const)
            (ACCFaulty l' e')  -> evalUpto eval stk (trace (l,s,Wrong) trc) (ACCFaulty l' e')
            (ACCCorrect l' e') -> evalUpto eval stk trc (ACCCorrect l' (Observed l s e'))
            (Let (x,e1) e2)    -> evalUpto eval stk trc (Let (x,e1) (Observed l s e2))
            _ -> do
              (stk',trc',e') <- evalUpto eval stk trc e
              case e' of
                Exception msg  -> return (stk',trc',Exception msg)
                Expression e'' -> evalUpto eval stk' trc' (Observed l s e'')

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
-- Algorithmic debugging from a trace.

faultyNodes :: Expr -> [Label]
faultyNodes = getLabels . (findFaulty wrongCC mergeCC) . mkGraph . (evalE eval)

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
propValidExpr e = let (_,_,e') = (evalE' eval) e in e' == Expression Const

propExact :: Expr -> Bool
propExact e = faultyNodes e == faultyExprs e

propSubset :: Expr -> Bool
propSubset e = (faultyNodes e) `subset` (faultyExprs e)

subset :: Eq a => [a] -> [a] -> Bool
subset xs ys = foldr ((&&) . (`elem` ys)) True xs

propFoundFaulty :: Expr -> Bool
propFoundFaulty e = faultyNodes e /= []

propIsWrong :: Expr -> Bool
propIsWrong e = case lookupT "toplevel" (evalE eval $ Observed "toplevel" [] e) of
  (Just Wrong) -> True
  _            -> False

lookupT :: Label -> Trace -> Maybe Value
lookupT l t = lookup l (zip ls vs)
  where (ls,_,vs) = unzip3 t

propFaultyIfWrong e = propIsWrong e ==> propFoundFaulty e

main = quickCheckWith args (\e -> propValidExpr e ==> propFaultyIfWrong e)
  where args = Args { replay          = Nothing
                    , maxSuccess      = 100000  -- number of tests
                    , maxDiscardRatio = 100
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
test2  = evalE eval $ Apply (Lambda "y" (Apply (                 (Lambda "z" ((Apply (Var "y") "z")))) "z")) "z"

test2b = evalE eval $ Apply (Lambda "y" (Apply (Let ("x",Const) (Lambda "z" ((Apply (Var "y") "z")))) "z")) "z"


test2c = evalE eval $ Apply ((Apply (Let ("z",Apply Const "x") (Lambda "z" (Apply ((Apply ((Apply (Var "x") "x")) "y")) "y"))) "z")) "z"

test2d = evalE eval $ Apply (ACCCorrect "E" (Apply (Let ("z",Apply Const "x") (Lambda "z" (Apply (ACCCorrect "O" (Apply (ACCCorrect "D" (Apply (Var "x") "x")) "y")) "y"))) "z")) "z"

-- lookup failed?

test3a = faultyNodes $ ACCFaulty "A" (ACCCorrect "B" Const)
test3b = (display showGraph) . mkGraph . evalE eval $ ACCFaulty "A" (ACCCorrect "B" Const)
-- test3c = (display showGraph) . rmCycles . mkGraph . evalE eval $ ACCFaulty "L" (ACCFaulty "L" (Var "z"))

e4 = ACCFaulty "O" (ACCCorrect "C" (Let ("y",Const) (ACCCorrect "R" (ACCCorrect "F" (Var "y")))))

test4a = (display showGraph) . mkGraph . evalE eval $ e4

test4b = evalE eval e4

e5 = ACCFaulty "OUTER" (ACCCorrect "INNER" (Let ("x",Const) (Var "x")))

e6 = ACCFaulty "A" (ACCCorrect "B" (ACCCorrect "C" (ACCFaulty "D" (Var "x"))))

test = (display showGraph) . (dagify mergeCC) . mkGraph . evalE eval
test' = (display showGraph) . mkGraph . evalE eval

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
