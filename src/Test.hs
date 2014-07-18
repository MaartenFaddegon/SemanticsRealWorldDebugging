import IntendedSemantics

import Control.Monad.State(liftM,liftM2,liftM3)
import Prelude hiding (Right)
import Test.QuickCheck
import Data.Graph.Libgraph
import Context

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
