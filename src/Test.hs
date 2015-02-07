import IntendedSemantics
import Control.Monad.State(liftM,liftM2,liftM3,liftM4)
import Prelude hiding (Right)
import Test.QuickCheck
import Test.QuickCheck.Property(succeeded, failed)
import Data.Graph.Libgraph

--------------------------------------------------------------------------------
-- Algorithmic debugging from a trace

faultyNodes :: [CompStmt] -> [[Label]]
faultyNodes trc = getLabels . oldest . findFaulty' . snd . mkGraph $ (Const Right, trc)

wrongNodes :: [CompStmt] -> [Label]
wrongNodes = (map stmtLabel) . (filter (\c -> case stmtRepr c of Wrong -> True; _ -> False))

nonRootNodes :: [CompStmt] -> [CompStmt]
nonRootNodes = filter (\c -> length (stmtStack c) > 1)

--------------------------------------------------------------------------------
-- List of faulty expressions (static analysis)

annotations :: Expr -> [Expr]
annotations (Const _)         = []
annotations (Var _)           = []
annotations (Lambda _ e)      = annotations e
annotations (Apply e _)       = annotations e
annotations (Let (_,e1) e2)   = annotations e1 ++ annotations e2
annotations (c@(CC _ _ e))    = c : annotations e

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
                   , liftM2 Lambda gen_name (gen_expr $ n-1)
                   , liftM4 mkFun  gen_name gen_label gen_jmt (gen_expr $ n-1)
                   , liftM2 Apply  (gen_expr $ n-1) gen_name
                   , liftM  Var    gen_name
                   , liftM3 mkLet  gen_name (gen_expr $ n-1 `div` 2)
                                            (gen_expr $ n-1 `div` 2)
                   ]
  where gen_label         = elements $ map (:[]) ['A'..'Z']
        gen_name          = elements $ map (:[]) ['x'..'z']
        gen_jmt           = elements [Right, Wrong]
        mkLet a e1 e2     = Let (a,e1) e2
        mkFun a lbl jmt e = let a' = a ++ "'" 
                            in Lambda a (Apply (CC lbl jmt (Lambda a' e)) a)

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

  arbitrary = sized gen_expr

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

-- For any set 'ys' from 'yss', the sets 'xs' and 'ys' share at least one element
anyElem :: Eq a => [a] -> [[a]] -> Bool
anyElem xs yss = all (`oneCommonElem` xs) yss

  where oneCommonElem :: Eq a => [a] -> [a] -> Bool
        oneCommonElem xs ys = any (`elem` xs) ys

isWrong (Const Wrong) = True
isWrong _             = False

isRight (Const Right) = True
isRight _             = False

when :: Bool -> Bool -> Bool
when testb cond = if cond then testb else True

sound :: Expr -> (Expr,Bool)
sound e = (r, -- If debugging found a faulty cost centre, we did mark some cost centre as faulty
              (if (faultyLblsFromTrc /= []) then (faultyLblsFromExpr /= []) else True)
              -- If one of the computation statements is wrong, there is a faulty cost centre
              && (if (wrongLblsFromTrc /= []) then (faultyLblsFromTrc /= []) else True)
              -- One of the cost-centres in the faulty node is actually faulty.
              && (faultyLblsFromExpr `anyElem` faultyLblsFromTrc)
           )
     where (r,trc) = (mkStmts . evaluate) e
           wrongLblsFromTrc   = wrongNodes  trc
           faultyLblsFromTrc  = faultyNodes trc
           faultyLblsFromExpr = faultyExprs e

sound_prop :: Expr -> Property
sound_prop e = let (r,isSound) = sound $ CC "root" Right (uniqueLabels e)
                   isValid     = case r of (Const _) -> True; _ -> False
               in  isValid ==> property isSound

main = quickCheckWith args sound_prop
  where args = Args { replay          = Nothing
                    , maxSuccess      = 100000  -- number of tests
                    , maxDiscardRatio = 100
                    , maxSize         = 1000   -- max subexpressions
                    , chatty          = True
                    }
