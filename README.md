# Algorithmic Debugging of Real-World Haskell Programs: Deriving Dependencies from the Cost Centre Stack

This are the executable semantics as described in the paper "Algorithmic
Debugging of Real-World Haskell Programs: Deriving Dependencies from the Cost
Centre Stack", Maarten Faddegon and Olaf Chitil to appear at PLDI 2015.

In the paper we define an executable semantics (Figure 17) and a QuickCheck
property (Section 6.6). The code in this repository supports the claim that
this property holds for over 100000 randomly generated expressions of up to
1000 subexpressions each.
