#!/bin/sh
set -e
echo "module GeneratedTransitions where"
echo "import Types"
echo "import Prelude hiding (Either(..))"
echo "edges :: [(Vertex, Vertex)]"
echo "edges = map (\(a, (b, (c, d)), (e, (f, (g, h)))) -> (Vertex a b c d, Vertex e f g h)) raw_edges"
echo "raw_edges"
/home/gi/cek/trunk/bin/coqc -R /home/gi/cek/CoRN CoRN generate_transitions.v | head -n 1
