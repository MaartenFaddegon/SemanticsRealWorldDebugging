module SimpleSemantics where

import Control.Monad.State

--------------------------------------------------------------------------------
-- Expressions

data Expr = Const     Int
          | Lambda    Name Expr
          | Apply     Expr Name
          | Var       Name
          | Let       (Name,Expr) Expr
          | Exception String
          deriving (Show,Eq)

--------------------------------------------------------------------------------
-- The state.


data Context = Context { heap           :: !Heap
                       , reductionCount :: !Int
                       , depth          :: !Int
                       , cxtLog         :: ![String]
                       }

doLog :: String -> State Context ()
doLog msg = modify $ \cxt -> cxt{cxtLog = (msg ++ "\n") : cxtLog cxt}

evalWith' :: (Expr -> State Context Expr) -> Expr -> (Expr,String)
evalWith' reduce redex =
  let (res,cxt) = runState (eval reduce redex) (Context [] 0 1 [])
  in  (res, foldl (++) "" . reverse . cxtLog $ cxt)

evalWith :: (Expr -> State Context Expr) -> Expr -> Expr
evalWith reduce redex = evalState (eval reduce redex) (Context [] 0 1 [])

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
type Heap = [(Name,Expr)]

insertHeap :: Name -> Expr -> State Context ()
insertHeap x e = modify $ \s -> s{heap = (x,e) : (heap s)}

deleteHeap :: Name -> State Context ()
deleteHeap x = modify $ \s -> s{heap = filter ((/= x) . fst) (heap s)}

lookupHeap :: Name -> State Context Expr
lookupHeap x = do 
  me <- fmap (lookup x . heap) get
  case me of
    Nothing -> return (Exception ("Lookup '" ++ x ++ "' failed"))
    Just e  -> return e

--------------------------------------------------------------------------------
-- Reduction rules

reduce :: Expr -> State Context Expr

reduce (Const v) = 
  return (Const v)

reduce (Lambda x e) = 
  return (Lambda x e)

reduce (Let (x,e1) e2) = do
  insertHeap x e1
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
    (Exception msg) -> do
      return (Exception msg)
    (Const v) -> do
      return (Const v)
    (Lambda y e) -> do
      return (Lambda y e)
    e -> do
      deleteHeap x
      v' <- eval reduce e
      case v' of
        Exception msg -> return (Exception msg)
        v -> do
          insertHeap x v
          eval reduce (Var x)

--------------------------------------------------------------------------------
-- Substituting variable names.

subst :: Name -> Name -> Expr -> Expr
subst n m (Const v)          = Const v
subst n m (Lambda n' e)      = Lambda (sub n m n') (subst n m e)
subst n m (Apply e n')       = Apply (subst n m e) (sub n m n')
subst n m (Var n')           = Var (sub n m n')
subst n m (Let (n',e1) e2)   = Let ((sub n m n'),(subst n m e1)) (subst n m e2)

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
