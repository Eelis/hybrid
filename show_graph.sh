#!/bin/sh
set -e
scons -j 2 thermostat.vo
./generate_transitions.sh > GeneratedTransitions.hs
runhaskell graph_to_dot.hs | neato -n -Elen=5 -Tpng > t.png
