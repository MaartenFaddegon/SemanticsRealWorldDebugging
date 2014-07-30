module Debug where
import Data.Graph.Libgraph
import Context

type Vertex value = [Record value]

mkGraph :: (Trace value,expr) -> (expr,Graph (Vertex value))
mkGraph (trc,reduct) = (reduct,mapGraph (\r->[r]) (mkGraph' trc))

mkGraph' :: Trace value -> Graph (Record value)
mkGraph' trace = Graph (head roots)
                       trace
                       (foldr (\r as -> as ++ (arcsFrom r trace)) [] trace)
  where roots = filter (\rec -> recordStack rec == []) trace

arcsFrom :: (Record value) -> Trace value -> [Arc (Record value)]
arcsFrom src trc = (map (Arc src)) . (filter couldDependOn) $ trc
  where couldDependOns = pushDependency src 
                         :  map (callDependency src) trc
                         ++ map (flip callDependency src) trc
        couldDependOn  = yna couldDependOns

        -- The reverse of any
        yna :: [a->Bool] -> a -> Bool
        yna ps x = or (map (\p -> p x) ps)


nextStack :: (Record value) -> Stack
nextStack rec = push (recordLabel rec) (recordStack rec)

pushDependency :: (Record value) -> (Record value) -> Bool
pushDependency p c = nextStack p == recordStack c

callDependency :: (Record value) -> (Record value) -> (Record value) -> Bool
callDependency p q c = call (nextStack p) (nextStack q) == recordStack c
