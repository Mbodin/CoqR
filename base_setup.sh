#!/bin/bash


for f in $1/Rlib/base/*; do
    echo "Adding file $f to initial state"
    cat $f | $1/src/runR.native -initial-state $1/Rlib/bootstrapping.state -final-state $1/Rlib/bootstrapping.state -hide-prompt
    echo "Finished including file to initial state"
done

