#!/bin/sh
set -e
echo "module GeneratedTransitions where"
echo "import Types"
echo "import Prelude hiding (Either(..))"
echo "edges :: [(Vertex, Vertex)]"
echo "edges = map (\(a, (b, c, d), (e, (f, g, h))) -> (Vertex (if a then Cont else Disc) b c d, Vertex (if e then Cont else Disc) f g h)) raw_edges"
echo "raw_edges"
coqc -R /data/home/eelis/soft/CoRN CoRN generate_transitions.v | head -n 1
