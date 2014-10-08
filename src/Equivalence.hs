import Prelude hiding (Right)
import IntendedSemantics(Judgement(..))
import qualified IntendedSemantics as I
import qualified TraceSemantics    as T
import Data.Graph.Libgraph
import Test.HUnit
import Test.Framework
import Test.Framework.Providers.HUnit
import Data.Monoid

------------------------------------------------------------------------------------------

main = defaultMainWithOpts
       [ testCase "e1 with 'g' faulty" test1a
       , testCase "e1 with 'h' faulty" test1b
       ] (mempty { ropt_color_mode = Just ColorNever })

------------------------------------------------------------------------------------------

type Label = String

evalT = snd . T.mkStmts . T.evaluate
evalI = snd . I.mkStmts . I.evaluate

translateTI :: [Label] -> T.Expr -> I.Expr
translateTI fs (T.Const i)       = I.Const Right
translateTI fs (T.Lambda n e)    = I.Lambda n (translateTI fs e)
translateTI fs (T.Apply e n)     = I.Apply (translateTI fs e) n
translateTI fs (T.Var n)         = I.Var n
translateTI fs (T.Let (n,e1) e2) = I.Let (n,translateTI fs e1) (translateTI fs e2)
translateTI fs (T.ACC l e)       
                   | l `elem` fs = I.ACCFaulty  l (translateTI fs e)
                   | otherwise   = I.ACCCorrect l (translateTI fs e)

judge :: [(String,Judgement)] -> [T.CompStmt] -> [I.CompStmt]
judge js = map judgeStmt
  where judgeStmt (T.CompStmt l s i v) = case lookup v js of
                                                (Just j) -> I.CompStmt l s i j
                                                _        -> error ("Need to judge " ++ v)

debug :: [I.CompStmt] -> [[Label]]
debug trc = getLabels . I.oldest . I.findFaulty' . snd . I.mkGraph $ (I.Const Right, trc)
  where getLabels = map (map I.stmtLabel)

debugI :: [Label] -> T.Expr -> [[Label]]
debugI fs = debug . evalI . (translateTI fs)

debugT :: [(Label,Judgement)] -> T.Expr -> [[Label]]
debugT js = debug . (judge js) . evalT

equivalent :: T.Expr -> [Label] -> [(Label,Judgement)] -> Assertion
equivalent e fs js = debugI fs e @?= debugT js e

(?) = (,)

------------------------------------------------------------------------------------------
--
-- Example 1: CC "main" (let h = CC "h" \f x . f x
--                           g = CC "g" \x . x
--                           i = 8
--                       in h g i
--                      )
--
--      Case a: bug in "g"
--      Case b: bug in "h"

e1t = T.ACC "main"
      ( T.Let ("h", T.ACC "h" $ T.Lambda "f" (T.Lambda "x"(T.Apply (T.Var "f") "x")))
      $ T.Let ("g", T.ACC "g" (T.Lambda "y" (T.Var "y")))
      $ T.Let ("i", (T.Const 8)) 
      $ T.Apply (T.Apply (T.Var "h") "g") "i"
      )

test1a = equivalent e1t ["g"] 
                [ "main = 8" ? Wrong
                , "h (\\8 -> 8) = (\\8 -> 8)" ? Right
                , "g 8 = 8" ? Wrong
                ]

test1b = equivalent e1t ["h"] 
                [ "main = 8" ? Wrong
                , "h (\\8 -> 8) = (\\8 -> 8)" ? Wrong
                , "g 8 = 8" ? Wrong
                ]
