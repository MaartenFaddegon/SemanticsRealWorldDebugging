import IntendedSemantics
import Control.Monad.State(liftM,liftM2,liftM3)
import Prelude hiding (Right)
import Test.QuickCheck
import Test.QuickCheck.Property(succeeded, failed)
import Data.Graph.Libgraph

--------------------------------------------------------------------------------
-- Algorithmic debugging from a trace

faultyNodes :: [CompStmt] -> [[Label]]
faultyNodes trc = getLabels . oldest . findFaulty' . snd . mkGraph $ (Const Right, trc)


--------------------------------------------------------------------------------
-- List of faulty expressions (static analysis)

faultyExprs :: Expr -> [Label]
faultyExprs (Const _)         = []
faultyExprs (Lambda _ e)      = faultyExprs e
faultyExprs (Apply e _)       = faultyExprs e
faultyExprs (Var _)           = []
faultyExprs (Let (_,e1) e2)   = faultyExprs e1 ++ faultyExprs e2
faultyExprs (CC _ Right e)    = faultyExprs e
faultyExprs (CC l Wrong e)    = l : faultyExprs e

--------------------------------------------------------------------------------
-- Generating arbitrary expressions

gen_expr :: Int -> Gen Expr
gen_expr 0 = elements [Const Right]
gen_expr n = oneof [ elements [Const Right]
                   , liftM2 Lambda     gen_name gen_expr'
                   , liftM2 Apply      gen_expr' gen_name
                   , liftM  Var        gen_name
                   , liftM3 mkLet      gen_name gen_expr' gen_expr'
                   , liftM3 CC         gen_label gen_jmt gen_expr'
                   ]
  where gen_expr' = gen_expr (n-1)
        mkLet n e1 e2 = Let (n,e1) e2
        gen_label = elements $ map (:[]) ['A'..'Z']
        gen_name  = elements $ map (:[]) ['x'..'z']
        gen_jmt   = elements [Right, Wrong]

-- generate random expression with chunks of the form '\x-> acc ...'
gen_exprWeak :: Int -> Gen Expr
gen_exprWeak 0 = elements [Const Right]
gen_exprWeak n = oneof [ elements [Const Right]
                       , liftM2 Lambda     gen_name  (oneof [gen_expr', gen_cc])
                       , liftM2 Apply      gen_expr' gen_name
                       , liftM  Var        gen_name
                       , liftM3 mkLet      gen_name  gen_expr' gen_expr'
                       ]
  where gen_expr' = gen_exprWeak (n-1)
        mkLet n e1 e2 = Let (n,e1) e2
        gen_label = elements $ map (:[]) ['A'..'Z']
        gen_name  = elements $ map (:[]) ['x'..'z']
        gen_jmt   = elements [Right, Wrong]
        gen_cc    = liftM3 CC gen_label gen_jmt gen_expr'

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
uniqueLabels' (l:lbls) (CC _ j e)        = let (lbls',e') = uniqueLabels' lbls e
                                           in (lbls',CC l j e')

instance Arbitrary Expr where

  arbitrary = sized gen_exprWeak

  shrink (Const j)        = []
  shrink (CC l j e)       = e : (map (CC l j) (shrink e))
  shrink (Lambda n e)     = e : (map (Lambda n) (shrink e))
  shrink (Apply e n)      = let alts = e : (map (flip Apply n) (shrink e))
                            in case e of
                              (Lambda _ e') -> e' : alts
                              _             -> alts
  shrink (Let (n,e1) e2)  = e2 : e1 
                            :    (map (Let (n,e1)) (shrink e2))
                            ++   (map (\e-> Let (n,e) e2) (shrink e1))
  shrink _                = [Const Right]

--------------------------------------------------------------------------------
-- Propositions

anyElem :: Eq a => [a] -> [[a]] -> Bool
anyElem ys = foldr ((&&) . any (`elem` ys)) True

isWrong (Const Wrong) = True
isWrong _             = False

isRight (Const Right) = True
isRight _             = False

when :: Bool -> Bool -> Bool
when testb cond = if cond then testb else True

sound :: Expr -> Property
sound e = valid ==> (    
          -- If the reduct is Wrong we marked some cost centre(s) as faulty.
          property (if (isWrong r) then (dynFCC /= []) else True)
          -- One of the cost-centres in the faulty node is actually faulty.
          .&&. property (statFCC `anyElem` dynFCC)
          )

  where (r,trc) = (mkStmts . evaluate) expr
        dynFCC  = faultyNodes trc
        statFCC = faultyExprs expr

        valid   = case r of (Const _) -> True; _ -> False
        expr    = CC "root" Right (uniqueLabels e)

main = quickCheckWith args sound
  where args = Args { replay          = Nothing
                    , maxSuccess      = 100000  -- number of tests
                    , maxDiscardRatio = 100
                    , maxSize         = 1000   -- max subexpressions
                    , chatty          = True
                    }
