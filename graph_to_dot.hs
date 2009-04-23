import GeneratedTransitions
import Types
import List (nub)
import Prelude hiding (Left, Right)

range_coordinate :: Range -> Double
range_coordinate r = case r of
  I01 -> 0; I12 -> 1; I23 -> 2; I34 -> 3; I45 -> 4
  OI_1 -> 0; OI12 -> 1; OI23 -> 2; OI34 -> 3; OI4_ -> 4
  CI0_D -> 0; CID_12 -> 0.1; CI12_1 -> 0.5; CI1_2 -> 1; CI2_3 -> 2; CI3_ -> 3
  TIC_45 -> 0; TI45_5 -> 4.5; TI5_6 -> 5; TI6_9 -> 6; TI9_10 -> 9; TI10_ -> 10

location_index :: Location -> Int
location_index l = case l of
  Up -> 0; Right -> 1; Down -> 2; Left -> 3
  Heat -> 0; Cool -> 1; Check -> 2

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
  show (100 + range_coordinate r * 600 + fromIntegral (kind_index k * 90)) ++ "," ++
  show (100 + range_coordinate r' * 200 + fromIntegral (kind_index k * 15) + fromIntegral (location_index l * 30)) ++ "\"]\n"

edge_visible :: Vertex -> Vertex -> Bool
edge_visible v@(Vertex k l r r') v'@(Vertex k' l' u u') =
  -- not (k == Cont && k' == Cont && vertices_adjacent v v') &&
  -- (l == Check || l' == Check) &&
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
