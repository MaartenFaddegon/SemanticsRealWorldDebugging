module Debug where
import Data.Graph.Libgraph
import Context

type Vertex value = [Record value] -- deriving (Eq,Ord,Show)

mkGraph :: Trace value -> Graph (Vertex value)
mkGraph trace = mapGraph (\r -> [r]) (mkGraph' trace)

mkGraph' :: Trace value -> Graph (Record value)
mkGraph' trace = Graph (last trace)
                       trace
                       (foldr (\r as -> as ++ (arcsFrom r trace)) [] trace)

arcsFrom :: (Record value) -> Trace value -> [Arc (Record value)]
arcsFrom src = (map (Arc src)) . (filter (src `couldDependOn`))

couldDependOn :: (Record value) -> (Record value) -> Bool
couldDependOn (l,s,_) (_,t,_) = push l s == t
