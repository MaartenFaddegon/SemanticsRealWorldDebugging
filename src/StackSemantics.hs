module StackSemantics where

import Control.Monad.State

--------------------------------------------------------------------------------
-- Expressions

data Expr = CC        Label Expr
          | Const     Int
          | Lambda    Name Expr
          | Apply     Expr Name
          | Var       Name
          | Let       (Name,Expr) Expr
          | Exception String
          deriving (Show,Eq)

--------------------------------------------------------------------------------
-- The state.

data Context = Context { stack          :: !Stack
                       , heap           :: !Heap
                       , depth          :: !Int
                       , reductionCount :: !Int
                       , reduceLog      :: ![String]
                       }

doLog :: String -> State Context ()
doLog msg = modify $ \cxt -> cxt{reduceLog = (msg ++ "\n") : reduceLog cxt}

evalWith' :: (Expr -> State Context Expr) -> Expr -> (Expr,String)
evalWith' reduce redex =
  let (res,cxt) = runState (eval reduce redex) (Context [] [] 0 1 [])
  in  (res, foldl (++) "" . reverse . reduceLog $ cxt)

evalWith :: (Expr -> State Context Expr) -> Expr -> Expr
evalWith reduce redex = evalState (eval reduce redex) (Context [] [] 0 1 [])

eval :: (Expr -> State Context Expr) -> (Expr -> State Context Expr)
eval reduce expr = do 
  n <- gets reductionCount
  modify $ \s -> s {reductionCount = n+1}
  if n > 500
    then return (Exception "Giving up after 500 reductions.")
    else do
        d <- gets depth
        modify $ \cxt -> cxt{depth=d+1}
        doLog (showd d ++ show n ++ ": " ++ show expr)
        reduct <- reduce expr
        modify $ \cxt -> cxt{depth=d}
        return reduct
  where showd 0 = ""
        showd n = '|' : showd (n-1)

--------------------------------------------------------------------------------
-- Manipulating the heap.

type Name = String
type Heap = [(Name,(Stack,Expr))]

insertHeap :: Name -> (Stack,Expr) -> State Context ()
insertHeap x e = modify $ \s -> s{heap = (x,e) : (heap s)}

deleteHeap :: Name -> State Context ()
deleteHeap x = modify $ \s -> s{heap = filter ((/= x) . fst) (heap s)}

lookupHeap :: Name -> State Context (Stack,Expr)
lookupHeap x = do 
  me <- fmap (lookup x . heap) get
  case me of
    Nothing -> return ([],Exception ("Lookup '" ++ x ++ "' failed"))
    Just (stk,e) -> return (stk,e)

--------------------------------------------------------------------------------
-- Stack handling: push and call.

type Label = String
type Stack = [Label]

setStack :: Stack -> State Context ()
setStack stk = modify $ \s -> s {stack = stk}

doPush :: Label -> State Context ()
doPush l = modify $ \s -> s {stack = push l (stack s)}

push :: Label -> Stack -> Stack
push l s
  | l `elem` s = dropWhile (/= l) s
  | otherwise  = l : s

doCall :: Stack -> State Context ()
doCall sLam = modify $ \s -> s {stack = call (stack s) sLam}

call :: Stack -> Stack -> Stack
-- MF TODO: look into this, call sApp sLam = sApp ++ sLam'
call sApp sLam =
       sNew

-- call sApp sLam = sNew
  where (sPre,sApp',sLam') = commonPrefix sApp sLam
        sNew = sLam' ++ sApp

commonPrefix :: Stack -> Stack -> (Stack, Stack, Stack)
commonPrefix sApp sLam
  = let (sPre,sApp',sLam') = span2 (==) (reverse sApp) (reverse sLam)
    in (sPre, reverse sApp', reverse sLam') 

span2 :: (a -> a -> Bool) -> [a] -> [a] -> ([a], [a], [a])
span2 f = s f []
  where s _ pre [] ys = (pre,[],ys)
        s _ pre xs [] = (pre,xs,[])
        s f pre xs@(x:xs') ys@(y:ys') 
          | f x y     = s f (x:pre) xs' ys'
          | otherwise = (pre,xs,ys)


--------------------------------------------------------------------------------
-- Reduction rules

reduce :: Expr -> State Context Expr

reduce (Const v) = 
  return (Const v)

reduce (Lambda x e) = 
  return (Lambda x e)

reduce (Let (x,e1) e2) = do
  stk <- gets stack
  insertHeap x (stk,e1)
  result <- reduce e2
  deleteHeap x
  return result

reduce (Apply f x) = do
  e <- eval reduce f
  case e of 
    (Lambda y e)  -> eval reduce (subst y x e)
    Exception msg -> return (Exception msg)
    _             -> return (Exception "Apply non-Lambda?")

reduce (Var x) = do
  r <- lookupHeap x
  case r of
    (_,Exception msg) -> do
      return (Exception msg)
    (stk,Const v) -> do
      setStack stk
      return (Const v)
    (stk,Lambda y e) -> do
      doCall stk
      return (Lambda y e)
    (stk,e) -> do
      deleteHeap x
      setStack stk
      v' <- eval reduce e
      case v' of
        Exception msg -> return (Exception msg)
        v -> do
          stkv <- gets stack
          insertHeap x (stkv,v)
          setStack stk
          eval reduce (Var x)

reduce (CC l e) = do
  stk <- gets stack
  doPush l
  eval reduce e

--------------------------------------------------------------------------------
-- Substituting variable names.

subst :: Name -> Name -> Expr -> Expr
subst n m (Const v)          = Const v
subst n m (Lambda n' e)      = Lambda (sub n m n') (subst n m e)
subst n m (Apply e n')       = Apply (subst n m e) (sub n m n')
subst n m (Var n')           = Var (sub n m n')
subst n m (Let (n',e1) e2)   = Let ((sub n m n'),(subst n m e1)) (subst n m e2)
subst n m (CC l e)           = CC l (subst n m e)

sub :: Name -> Name -> Name -> Name
sub n m n' = if n == n' then m else n'

--------------------------------------------------------------------------------
-- Examples.

e1 = (Const 42)

e2 = Let ("x", Const 42) (Var "x")

e3 = Let ("i", (Const 42)) 
         (Apply (Lambda "x" (Var "x")) "i")

e4 = Let ("i", (Const 42)) 
         (Apply (Lambda "x" (Const 1)) "i")

e5 = Let ("i", (Const 42)) 
            ( Let ("id",Lambda "y" (Var "y"))
                  ( Apply 
                    ( Apply 
                      ( Lambda "f" 
                        ( Lambda "x"
                          ( Apply (Var "f") "x"
                          )
                        )
                      ) "id"
                    ) "i"
                  )
            )
