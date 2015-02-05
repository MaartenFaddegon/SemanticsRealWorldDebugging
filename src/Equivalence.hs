-- In this file we explain the equivalence between our intended semantics (with
-- judgements encoded into the expression) and judging computation statements
-- from our trace semantics.

import qualified TraceSemantics    as T
import qualified IntendedSemantics as I
import IntendedSemantics(Label)
import Data.Graph.Libgraph(Judgement(..))

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
                   | l `elem` fs = I.CC l Wrong (translateTI fs e)
                   | otherwise   = I.CC l Right (translateTI fs e)
translateTI fs (T.Plus e1 e2)    = I.Plus (translateTI fs e1) (translateTI fs e2)


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
                                                (Just j) -> I.CompStmt l s i j v
                                                _        -> error ("Need to judge \"" ++ v ++ "\"")

-- Secondly we build a computation graph and use algorithmic debugging to find the
-- label(s) of cost centre's whose expressions are identified as faulty.

debug :: [I.CompStmt] -> [[Label]]
debug trc = I.getLabels . I.oldest . I.findFaulty' . snd . I.mkGraph $ (I.Const Right, trc)

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
-- We use the following shorthand notations in the examples:

λ = T.Lambda
λ2 a1 a2 b = λ a1 (λ a2 b)
λ3 a1 a2 a3 b = λ a1 (λ2 a2 a3 b)
ap fn a = T.Apply (T.Var fn) a
ap2 fn a1 a2 = T.Apply (ap fn a1) a2
ap3 fn a1 a2 a3 = T.Apply (ap2 fn a1 a2) a3
ap' f a = T.Apply f a
ap2' f a1 a2 = T.Apply (ap' f a1) a2
ap3' f a1 a2 a3 = T.Apply (ap2' f a1 a2) a3
cc = T.ACC
var = T.Var
val = T.Const


------------------------------------------------------------------------------------------
--
-- Example 0: let dbl x = (\x' -> cc "dbl" x') x
--                i = 4
--            in cc "main" id i
--            


e0t = T.Let (dbl, λ x' (ap' (cc "dbl" (λ x (var x))) x'))
    $ T.Let (i, val 4)
    $ cc "main" (ap dbl i)
  where dbl = "dbl"; dbl'="dbl'"; x="x"; x'="x'"; i="i"

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
--
-- Example 3: let foldr1 = CC+ "foldr" \f z xs . f z xs 
--                foldr2 = CC+ "foldr" \f z xs . f xs (foldr1 f z xs)
--                insert = CC- "insert" \x xs = x + xs
--                isort  = CC+ "isort" \xs . foldr2 insert xs xs
--                ys = ☺
--            in  CC "main" isort ys

e3t = T.Let (foldr1, λ3 f' z' xs' (ap3' (T.ACC "foldr"  (λ3 f z xs (ap2 f z xs))
                                        ) f' z' xs'))
    $ T.Let (foldr2, λ3 f' z' xs' (ap3' (T.ACC "foldr"  (λ3 f z xs (T.Let (xs'',(ap3 foldr1 f z xs))
                                                                          (ap2 f xs xs'')))
                                        ) f' z' xs'))
    $ T.Let (insert, λ2 x' xs'    (ap2' (T.ACC "insert" (λ2 x xs   (x + xs))
                                        ) x' xs'))
    $ T.Let (isort,  λ xs'        (ap'  (T.ACC "isort"  (λ xs      (ap3 foldr2 insert xs xs))
                                        ) xs'))
    $ T.Let (ys,     T.Const 7)
    $ T.ACC "main" (ap isort ys)

  where f = "f"; f'="f'"; z="z"; z'="z'"; x="x"; x'="x'"; xs="xs"; xs'="xs'"; xs''="xs''"; ys="ys"
        foldr1="foldr1"; foldr2="foldr2"; insert="insert"; isort="isort"
        (+) n m = T.Plus (T.Var n) (T.Var m)

test3a = equivalent e3t ["insert"] 
                [ "main = 21" ? Wrong
                , "isort 7 = 21" ? Wrong
                , "insert 7 = (\\7 -> 14)" ? Wrong
                , "insert 7 = (\\14 -> 21)" ? Wrong
                , "foldr (\\7 -> (\\7 -> 14)) = (\\7 -> (\\7 -> 14))" ? Right
                , "foldr {(\\7 -> (\\7 -> 14)); (\\7 -> (\\14 -> 21))} = (\\7 -> (\\7 -> 21))" ? Right
                ]

------------------------------------------------------------------------------------------
--
-- Example 4: let i         = 2
--                dbl x'    = (\x -> cc "dbl" (x+x)) x'
--                twc f' x' = (\f x -> cc "twc" f x) f x
--            in cc "main" id i
-- 
e4t = T.Let (i, val 2)
    $ T.Let (dbl, λ x' (ap' (cc "dbl" (λ x (x + x))) x'))
    $ T.Let (twc, λ2 f' x' (ap2' (cc "twc" (λ x (var x))) f' x'))
    $ cc "main" (ap2 twc dbl i)

  where dbl = "dbl"; dbl'="dbl'"; x="x"; x'="x'"; i="i"; twc = "twc"; twc'="twc'"
        (+) n m = T.Plus (T.Var n) (T.Var m); f = "f"; f'="f'";

------------------------------------------------------------------------------------------
--
-- Example 5: let f = cc "f" let g = cc "g" \x -> x+x
--                           in "f_in" \y -> f y
--                k = 3
--            in cc "main" (f k)


e5t :: T.Expr
e5t = cc "caf"
    $ T.Let (f, cc "f" (T.Let (g, (λ x (T.Plus (T.Var x) (val 1))))
                       (λ y' (ap' (cc "f_in" (λ y (ap g y))) y')))) 
    $ T.Let (i, val 3)
    $ T.Let (j, cc "j" (ap f i))
    $ cc "main" (ap f j)
    
  where i = "i"; j = "j"; f = "f"; g = "g"; x = "x"; x' = "x'"; 
        y = "y"; y' = "y'"; z' = "z'"

------------------------------------------------------------------------------------------
--
-- Example 6: After initial questions by anonymous reviewers from PLDI
--
-- a)     let h = push "h" (\f -> let {fourty=fourty} f fourty)
--            f = (\x -> x)
--        in h f
--
-- b)     let h = push "h" (\f x -> let {y=-40} x+f+y )
--            fourty = 40
--            f = h(fourty)
--        in  f fourty
--
-- c)     let f = push "f" \x. x+1
--            g = push "g" \x. (f x)+(f x)
--            o = 1
--         in g o
--

e6ta = cc "caf"
     $ T.Let (h, cc "h" (λ f (T.Let (fourty, (val 40)) (ap f fourty))))
     $ T.Let (f, λ x (var x))
     $ cc "main" (ap h f)
     where f = "f"; h = "h"; fourty="fourty"; x="x"

e6tb = cc "caf"
     $ T.Let (h, cc "h" (λ2 f x (T.Let (y, (val (-40))) ((var x) + (var f) + (var y)))))
     $ T.Let (fourty, val 40)
     $ T.Let (f, ap h fourty)
     $ cc "main" (ap f fourty)

     where f = "f"; h = "h"; fourty="fourty"; x="x"; y="y"
           (+) n m = T.Plus n m

et6c = cc "caf"
     $ T.Let (f, cc "f" (λ x (var x + var x)))
     $ T.Let (g, cc "g" (λ x (ap f x + ap f x)))
     $ T.Let (o, val 1)
     $ cc "main" (ap g o)
     where f = "f"; g = "g"; o="o"; x="x"; y="y"
           (+) n m = T.Plus n m

et6d = T.Let (f, (λ x (ap' (cc "f" (λ y (var y + var y))) x)))
     $ T.Let (g, (λ x (ap' (cc "g" (λ y (ap f y))) x)))
     $ T.Let (o, val 1)
     $ cc "main" (ap g o)
     where f = "f"; g = "g"; o="o"; x="x"; y="y"
           (+) n m = T.Plus n m
------------------------------------------------------------------------------------------
--
-- Example 7: After final feedback from anonymous reviewers from PLDI
--
--        let constant = 21
--            double   = \x'    -> (push "double" \x   -> x + x) x'
--            lift     = \x' f' -> (push "lift"   \x f -> f x) x' f'
--            unlift   = \p'    -> (push "unlift" \p   -> let f = \x -> x in p f) p'
--            g        = \h'     -> (push "g" let j = \x -> double x
--                                                p = lift j
--                                            in  \h -> push "g1" (h p)) h'
--            main     = \x' -> push "main" let h \p -> (unlift p) constant
--                                          in \x -> push "main1" (g h)) x'
--            o        = 1
--        in main o

et7 = T.Let  (constant, val 21)
    $ T.Let  (double, λ x'     $ ap'  (cc "double" (λ x (x + x))) x')
    $ T.Let  (lift,   λ2 x' f' $ ap2' (cc "lift" (λ2 x f (ap f x))) x' f')
    $ T.Let  (unlift, λ p'     $ ap'  (cc "unlift" (λ p (T.Let (f, (λ x (var x)))
                                                  {-in-} (ap p f)))) p')
    $ T.Let  (g,      λ h'     $ ap'  (cc "g" ( T.Let  (j, (λ x (ap double x)))
                                              $ T.Let  (p, ap lift j)
                                              $ {-in-} (λ h (cc "g1" (ap h p))))) h')
    $ T.Let  (main,   λ h' $ ap' (cc "main" ( T.Let  (h, λ p (ap' (ap unlift p) constant))
                                              {-in-} (λ x (cc "main1" (ap g h))))) h')
    $ T.Let  (o, val 1)
    $ {-in-} (ap main o)

    where constant = "constant"; x = "x"; x' = "x'"; f = "f"; f' = "f'"; p = "p"; p' = "p'" 
          double = "double"; lift = "lift"; unlift = "unlift"; g = "g"; j = "j"; h = "h"; h' = "h'"
          main = "main"; o = "o"
          (+) n m = T.Plus (var n) (var m)

------------------------------------------------------------------------------------------

main = defaultMainWithOpts
       [ testCase "e1 fault in 'g'"    test1a
       , testCase "e1 fault in 'h'"    test1b
       , testCase "e2 fault in 'f'"    test2a
       , testCase "e2 fault in 'g'"    test2b
       , testCase "e2 fault in 'main'" test2c
       , testCase "e3 fault in insert" test3a
       ] (mempty { ropt_color_mode = Just ColorNever })

(?) = (,)
