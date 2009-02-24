import GeneratedTransitions
import Types
import List (nub)
import Prelude hiding (Left, Right)

range_coordinate :: Range -> Int
range_coordinate r = case r of I01 -> 0; I12 -> 1; I23 -> 2; I34 -> 3; I45 -> 4

location_index :: Location -> Int
location_index l = case l of Up -> 0; Right -> 1; Down -> 2; Left -> 3

kind_index :: Kind -> Int
kind_index Cont = 0; kind_index Disc = 1

ranges_adjacent :: Range -> Range -> Bool
ranges_adjacent r r' = abs (range_coordinate r - range_coordinate r') <= 1

vertices_adjacent :: Vertex -> Vertex -> Bool
vertices_adjacent (Vertex _ _ a a') (Vertex _ _ b b') =
  ranges_adjacent a b && ranges_adjacent a' b'

pos_label :: Vertex -> String
pos_label (Vertex k l r r') = "[label=\"" ++ show l ++ "\",color=" ++
  (if k == Cont then "red" else "blue") ++ ",pos=\"" ++
  show (100 + range_coordinate r * 200 + kind_index k * 50) ++ "," ++
  show (100 + range_coordinate r' * 200 + kind_index k * 5 + location_index l * 30) ++ "\"]\n"

edge_visible :: Vertex -> Vertex -> Bool
edge_visible v@(Vertex k l r r') v'@(Vertex k' l' u u') =
  -- not (k == Cont && k' == Cont && vertices_adjacent v v') &&
  -- (l == Up || l' == Up) &&
  True

visible_edges :: [(Vertex, Vertex)]
visible_edges = filter (uncurry edge_visible) edges

main = putStrLn $
  "digraph {\n"
  ++ concatMap (\s -> show (show s) ++ pos_label s)
    (nub $ map fst visible_edges ++ map snd visible_edges)
  ++ concatMap (\(s@(Vertex k _ _ _), s') -> show (show s) ++ " -> " ++ show (show s') ++
    "[color=" ++ (if k == Cont then "red" else "blue") ++ "]\n") visible_edges
  ++ "}"
