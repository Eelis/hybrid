#!/bin/sh
coqdep -R . hybrid -I . -I examples/thermostat *.v examples/thermostat/*.v 2> /dev/null | runhaskell coqdeps_as_dot.hs | dot -Tpng > deps.png
