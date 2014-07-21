module Debug where
import Data.Graph.Libgraph
import Context

type Vertex value = [Record value]

mkGraph :: (expr,Trace value) -> (expr,Graph (Vertex value))
mkGraph (reduct,trace) = (reduct,mapGraph (\r->[r]) (mkGraph' trace))

mkGraph' :: Trace value -> Graph (Record value)
mkGraph' trace = Graph (head roots)
                       trace
                       (foldr (\r as -> as ++ (arcsFrom r trace)) [] trace)
  where roots = filter (\(_,stk,_) -> stk == []) trace

arcsFrom :: (Record value) -> Trace value -> [Arc (Record value)]
arcsFrom src = (map (Arc src)) . (filter (src `couldDependOn`))

couldDependOn :: (Record value) -> (Record value) -> Bool
couldDependOn (l,s,_) (_,t,_) = push l s == t
