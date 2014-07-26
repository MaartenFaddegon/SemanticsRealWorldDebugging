import IntendedSemantics

import Control.Monad.State(liftM,liftM2,liftM3)
import Prelude hiding (Right)
import Test.QuickCheck
import Data.Graph.Libgraph
import Context
import Debug

--------------------------------------------------------------------------------
-- Algorithmic debugging from a trace

faultyNodes :: Expr -> [Label]
faultyNodes = getLabels . findFaulty' . snd . mkGraph . mkEquations . (evalWith reduce)

getLabels :: [Vertex Judgement] -> [Label]
getLabels = foldl accLabels []
  where accLabels acc v = acc ++ getLabels' v
        getLabels' = map recordLabel


--------------------------------------------------------------------------------
-- List of faulty expressions (static analysis)

faultyExprs :: Expr -> [Label]
faultyExprs (Const _)         = []
faultyExprs (Lambda _ e)      = faultyExprs e
faultyExprs (Apply e _)       = faultyExprs e
faultyExprs (Var _)           = []
faultyExprs (Let (_,e1) e2)   = faultyExprs e1 ++ faultyExprs e2
faultyExprs (ACCCorrect _ e)  = faultyExprs e
faultyExprs (ACCFaulty l e)   = l : faultyExprs e

--------------------------------------------------------------------------------
-- Generating arbitrary expressions

gen_expr :: Int -> Gen Expr
gen_expr 0 = elements [Const Right]
gen_expr n = oneof [ elements [Const Right]
                   , liftM2 Lambda     gen_name gen_expr'
                   , liftM2 Apply      gen_expr' gen_name
                   , liftM  Var        gen_name
                   , liftM3 mkLet      gen_name gen_expr' gen_expr'
                   , liftM2 ACCCorrect gen_label gen_expr'
                   , liftM2 ACCFaulty  gen_label gen_expr'
                   ]
  where gen_expr' = gen_expr (n-1)
        mkLet n e1 e2 = Let (n,e1) e2
        gen_label = elements $ map (:[]) ['A'..'Z']
        gen_name  = elements $ map (:[]) ['x'..'z']

gen_exprWeak :: Int -> Gen Expr
gen_exprWeak 0 = elements [Const Right]
gen_exprWeak n = oneof [ elements [Const Right]
                       , liftM2 Lambda     gen_name gen_acc
                       , liftM2 Apply      gen_expr' gen_name
                       , liftM  Var        gen_name
                       , liftM3 mkLet      gen_name gen_expr' gen_expr'
                       ]
  where gen_expr' = gen_exprWeak (n-1)
        mkLet n e1 e2 = Let (n,e1) e2
        gen_label = elements $ map (:[]) ['A'..'Z']
        gen_name  = elements $ map (:[]) ['x'..'z']
        gen_acc   = oneof [ liftM2 ACCCorrect gen_label gen_expr'
                          , liftM2 ACCFaulty  gen_label gen_expr'
                          ]

uniqueLabels :: Expr -> Expr
uniqueLabels e = snd (uniqueLabels' lbls e)
  where lbls = zipWith (++) (cycle ["CC"]) (map show [1..])

uniqueLabels' lbls (Const v)             = (lbls,Const v)
uniqueLabels' lbls (Lambda n e)          = let (lbls',e') = uniqueLabels' lbls e
                                           in (lbls',Lambda n e')
uniqueLabels' lbls (Apply e n)           = let (lbls',e') = uniqueLabels' lbls e
                                           in (lbls',Apply e' n)
uniqueLabels' lbls (Var n)               = (lbls,Var n)
uniqueLabels' lbls (Let (n,e1) e2)       = let (lbls1,e1') = uniqueLabels' lbls  e1
                                               (lbls2,e2') = uniqueLabels' lbls1 e2
                                           in (lbls2,Let (n,e1') e2')
uniqueLabels' (l:lbls) (ACCCorrect _ e)  = let (lbls',e') = uniqueLabels' lbls e 
                                           in (lbls',ACCCorrect l e')
uniqueLabels' (l:lbls) (ACCFaulty _ e)   = let (lbls',e') = uniqueLabels' lbls e
                                           in (lbls',ACCFaulty l e')

instance Arbitrary Expr where
  arbitrary = sized gen_exprWeak
  shrink (ACCFaulty l e)  = e : (map (ACCFaulty l) (shrink e))
  shrink (ACCCorrect l e) = e : (map (ACCCorrect l) (shrink e))
  shrink (Lambda n e)     = e : (map (Lambda n) (shrink e))
  shrink (Apply e n)      = e : (map (flip Apply n) (shrink e))
  shrink (Let (n,e1) e2)  = e2 : e1 
                            :    (map (Let (n,e1)) (shrink e2))
                            ++   (map (\e-> Let (n,e) e2) (shrink e1))
  shrink (Var _)          = [Const Right]
  shrink _                = []
  

--------------------------------------------------------------------------------
-- Propositions

-- MF TODO: should we really allow any redex that doesn't throw an expression?
propValidExpr :: Expr -> Bool
propValidExpr e = case snd (evalWith reduce e) of Expression _ -> True; _ -> False

propExact :: Expr -> Bool
propExact e = faultyNodes e == faultyExprs e

propSubset :: Expr -> Bool
propSubset e = (faultyNodes e) `subset` (faultyExprs e)

subset :: Eq a => [a] -> [a] -> Bool
subset xs ys = foldr ((&&) . (`elem` ys)) True xs

propFoundFaulty :: Expr -> Bool
propFoundFaulty e = faultyNodes e /= []

propIsWrong :: Expr -> Bool
propIsWrong e = case snd (evalWith reduce e) of
  (Expression (Const Wrong)) -> True
  _                          -> False

propFaultyIfWrong e = propIsWrong e ==> propFoundFaulty e

sound e = propValidExpr e' ==> propFaultyIfWrong e'
  where e'   = ACCCorrect "root" (uniqueLabels e)

main = quickCheckWith args sound
  where args = Args { replay          = Nothing
                    , maxSuccess      = 100000  -- number of tests
                    , maxDiscardRatio = 100
                    , maxSize         = 1000    -- max subexpressions
                    , chatty          = True
                    }
