#!/bin/sh
set -e
./generate_transitions.sh > GeneratedTransitions.hs
runhaskell graph_to_dot.hs | neato -n -Elen=5 -Tpng > t.png
