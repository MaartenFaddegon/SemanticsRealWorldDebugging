-- In this file we explain the equivalence between our intended semantics (with
-- judgements encoded into the expression) and judging computation statements
-- from our trace semantics.

import qualified TraceSemantics    as T
import qualified IntendedSemantics as I
import IntendedSemantics(Judgement(..),Label)

import Prelude hiding (Right)
import Data.Graph.Libgraph
import Test.HUnit
import Test.Framework
import Test.Framework.Providers.HUnit
import Data.Monoid

------------------------------------------------------------------------------------------
--
-- IntendedSemantics expressions are different from TraceSemantics expressions:
-- judgement on expressions enclosed by cost centres is encoded.
-- We define a function to translate a TraceSemantic expression, and a list of
-- labels of faulty cost centres into an IntendedSemantics expression.


translateTI :: [Label] -> T.Expr -> I.Expr
translateTI fs (T.Const i)       = I.Const Right
translateTI fs (T.Lambda n e)    = I.Lambda n (translateTI fs e)
translateTI fs (T.Apply e n)     = I.Apply (translateTI fs e) n
translateTI fs (T.Var n)         = I.Var n
translateTI fs (T.Let (n,e1) e2) = I.Let (n,translateTI fs e1) (translateTI fs e2)
translateTI fs (T.ACC l e)       
                   | l `elem` fs = I.ACCFaulty  l (translateTI fs e)
                   | otherwise   = I.ACCCorrect l (translateTI fs e)

------------------------------------------------------------------------------------------
--
-- Now let us define how a "conventional" algorithmic debugging session finds faults:
-- First we need to judge correctness of computation statements, the function 'judge'
-- does this by converting a list of TraceSemantic computation statements into a list
-- of IntendedSemantics computation statements. The first argument is a list of
-- representation and judgement tuples.

judge :: [(String,Judgement)] -> [T.CompStmt] -> [I.CompStmt]
judge js = map judgeStmt
  where judgeStmt (T.CompStmt l s i v) = case lookup v js of
                                                (Just j) -> I.CompStmt l s i j
                                                _        -> error ("Need to judge " ++ v)

-- Secondly we build a computation graph and use algorithmic debugging to find the
-- label(s) of cost centre's whose expressions are identified as faulty.

debug :: [I.CompStmt] -> [[Label]]
debug trc = getLabels . I.oldest . I.findFaulty' . snd . I.mkGraph $ (I.Const Right, trc)
  where getLabels = map (map I.stmtLabel)

-- Now we are ready to find faults in a TraceSemantic expression, using
-- a list of computation statement representations and their judgement.
-- Usually this judgement is obtained from the user.

debugT :: [(String,Judgement)] -> T.Expr -> [[Label]]
debugT js = debug . (judge js) . evalT
  where evalT = snd . T.mkStmts . T.evaluate

-- Next a key step to showing equivalence: we translate a TraceSemantic 
-- expression to an IntendedSemantics expression and then find faults
-- using the encoded judgements.

debugI :: [Label] -> T.Expr -> [[Label]]
debugI fs = debug . evalI . (translateTI fs)
  where evalI = snd . I.mkStmts . I.evaluate

-- Finally, we assert that debugging a TraceSemantic expression gives the same
-- result as debugging the IntededSemantic expression to which it translates.

equivalent :: T.Expr                    -- The expression (without intention encoded).
           -> [Label]                   -- The list of cost centres to be encoded as faulty.
           -> [(String,Judgement)]      -- The list of computation-statement representations
                                        -- and their judgements.
           -> Assertion
equivalent e fs js = debugI fs e @?= debugT js e

------------------------------------------------------------------------------------------
--
-- Example 1: CC "main" (let h f' = (CC "h" \f y . f y) f'
--                           g x = (CC "g" \y . y) x
--                           i = 8
--                       in h g i
--                      )
--
-- Demonstrating interaction between a higher-order (here h, could be map or foldl)
-- and a first-order function (here f, could be +1 or ++).
--
--      Case a: fault in "g"
--      Case b: fault in "h"

e1t = T.Let ("h", T.Lambda "f'" (T.Apply 
              (T.ACC "h" $ T.Lambda "f" (T.Lambda "x"(T.Apply (T.Var "f") "x"))) "f'"))
    $ T.Let ("g", (T.Lambda "x" (T.Apply (T.ACC "g" (T.Lambda "y" (T.Var "y"))) "x")))
    $ T.Let ("i", (T.Const 8)) 
    $ T.ACC "main" 
    $ T.Apply (T.Apply (T.Var "h") "g") "i"

test1a = equivalent e1t ["g"] 
                [ "main = 8" ? Wrong
                , "h (\\8 -> 8) = (\\8 -> 8)" ? Right
                , "g 8 = 8" ? Wrong
                ]

test1b = equivalent e1t ["h"] 
                [ "main = 8" ? Wrong
                , "h (\\8 -> 8) = (\\8 -> 8)" ? Wrong
                , "g 8 = 8" ? Right
                ]

------------------------------------------------------------------------------------------
--
-- Example 2: let f x = (CC "f" \y -> y) x
--                g x = (CC "g" \y -> g y) x
--                i = 3
--            in  CC "main" (g 3)
--
-- Demonstrate a simple chain of dependencies.
--
--      Case a: fault in "f"
--      Case b: fault in "g"
--      Case c: fault in "main"

e2t = T.Let ("f", T.Lambda "x" (T.Apply (T.ACC "f" (T.Lambda "y" (T.Var "y"))) "x"))
    $ T.Let ("g", T.Lambda "x" (T.Apply (T.ACC "g" (T.Lambda "y" (T.Apply (T.Var "f") "y"))) "x"))
    $ T.Let ("i", T.Const 3)
    $ T.ACC "main" (T.Apply (T.Var "g") "i")

test2a = equivalent e2t ["f"] 
                [ "main = 3" ? Wrong
                , "g 3 = 3" ? Wrong
                , "f 3 = 3" ? Wrong
                ]

test2b = equivalent e2t ["g"] 
                [ "main = 3" ? Wrong
                , "g 3 = 3" ? Wrong
                , "f 3 = 3" ? Right
                ]
test2c = equivalent e2t ["main"] 
                [ "main = 3" ? Wrong
                , "g 3 = 3" ? Right
                , "f 3 = 3" ? Right
                ]

------------------------------------------------------------------------------------------

main = defaultMainWithOpts
       [ testCase "e1 fault in 'g'"    test1a
       , testCase "e1 fault in 'h'"    test1b
       , testCase "e2 fault in 'f'"    test2a
       , testCase "e2 fault in 'g'"    test2b
       , testCase "e2 fault in 'main'" test2c
       ] (mempty { ropt_color_mode = Just ColorNever })

(?) = (,)
