module FreeVar(freeVars,FreeVar(..)) where
import IntendedSemantics
import Prelude hiding ((||),any,Right)
import Data.Graph.Libgraph

data FreeVar = NoFreeVar | FreeVar String 
  deriving (Show, Eq)

freeVars :: Expr -> FreeVar
freeVars = freeVars' [] []

freeVars' :: [String] -> [String] -> Expr -> FreeVar
freeVars' fs _  (CC         _ _ e)     = freeVars' fs [] e
freeVars' fs vs (Lambda     n e)       = freeVars' fs (n:vs) e
freeVars' fs vs (Apply      e n)       = if n `elem` (fs++vs) then freeVars' fs vs e 
                                                              else (FreeVar n)
freeVars' fs vs (Var        n)         = if n `elem` (fs++vs) then NoFreeVar    
                                                              else (FreeVar n)
freeVars' fs vs (Let        (n,e1) e2)
  | isFun e1                          = freeVars' (n:fs) vs     e1 || freeVars' (n:fs) vs     e2
  | otherwise                         = freeVars' fs     (n:vs) e1 || freeVars' fs     (n:vs) e2
freeVars' fs vs (Const      _)        = NoFreeVar

(||) :: FreeVar -> FreeVar -> FreeVar
(FreeVar v)  || _            = FreeVar v
_            || (FreeVar v)  = FreeVar v
_            || _            = NoFreeVar

any :: (a->FreeVar) -> [a] -> FreeVar
any f = foldl (\z x -> z || f x) NoFreeVar

isFun :: Expr -> Bool
isFun Lambda{}          = True
isFun (CC _ _ Lambda{}) = True
isFun _                 = False
