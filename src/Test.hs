import IntendedSemantics
import Control.Monad.State(liftM,liftM2,liftM3)
import Prelude hiding (Right)
import Test.QuickCheck
import Test.QuickCheck.Property(succeeded, failed)
import Data.Graph.Libgraph

--------------------------------------------------------------------------------
-- Algorithmic debugging from a trace

-- faultyNodes :: Expr -> [[Label]]
-- faultyNodes = getLabels . oldest . findFaulty' . snd . mkGraph . mkCompStmts . evaluate

faultyNodes :: [CompStmt] -> [[Label]]
faultyNodes trc = getLabels . oldest . findFaulty' . snd . mkGraph $ (Const Right, trc)

getLabels :: [[CompStmt]] -> [[Label]]
getLabels = map (map stmtLabel)

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

-- generate random expression with chunks of the form '\x-> acc ...'
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
        gen_acc   = frequency [ (1, liftM2 ACCCorrect gen_label gen_expr')
                              , (5, liftM2 ACCFaulty  gen_label gen_expr')
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

  shrink (Const j)        = []
  shrink (ACCFaulty l e)  = e : (map (ACCFaulty l) (shrink e))
  shrink (ACCCorrect l e) = e : (map (ACCCorrect l) (shrink e))
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
sound e = valid ==> (classify (trc == [])     "Trivial trace")
          $         (classify (statFCC == []) "Trivial expression")
          $         (classify (isWrong r)     "Reduces to 'Const Wrong'")
          $         (classify (isRight r)     "Reduces to 'Const Right'")

          (    -- If the reduct is Wrong we marked some cost centre(s) as faulty.
               property (if (isWrong r) then (dynFCC /= []) else True)
                
               -- One of the cost-centres in the faulty node is actually faulty.
          .&&. property (statFCC `anyElem` dynFCC)
          )

  where (r,trc) = (mkStmts . evaluate) expr
        dynFCC  = faultyNodes trc
        statFCC = faultyExprs expr

        valid   = case r of (Const _) -> True; _ -> False
        expr      = ACCCorrect "root" (uniqueLabels e)

main = quickCheckWith args sound
  where args = Args { replay          = Nothing
                    , maxSuccess      = 5000  -- number of tests
                    , maxDiscardRatio = 100
                    , maxSize         = 1000   -- max subexpressions
                    , chatty          = True
                    }
