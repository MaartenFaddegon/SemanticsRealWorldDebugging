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
  where couldDependOns = couldDependOn1 src 
                         :  map (couldDependOn2 src) trc
                         ++ map (flip couldDependOn2 src) trc
        couldDependOn  = yna couldDependOns

        -- The reverse of any
        yna :: [a->Bool] -> a -> Bool
        yna ps x = or (map (\p -> p x) ps)

couldDependOn1 :: (Record value) -> (Record value) -> Bool
couldDependOn1 p c = push (recordLabel p) (recordStack p) == recordStack c

couldDependOn2 :: (Record value) -> (Record value) -> (Record value) -> Bool
couldDependOn2 p1 p2 c = let s = push (recordLabel p1) (recordStack p1)
                             t = push (recordLabel p2) (recordStack p2)
                         in call s t == recordStack c



