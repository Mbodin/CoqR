#!/bin/bash

echo "Running tests for FastR - $1"

make

cp Rlib/bootstrapping.state Rlib/bootstrapping.initial.state

echo "Including base library for $1 tests"

for f in Rlib/fastr_oracle/$1/*; do
    echo "Adding file $f to initial state"
    cat $f | ./src/runR.native -initial-state Rlib/bootstrapping.state -final-state Rlib/bootstrapping.state -hide-prompt
    echo "Finished including file to initial state"
done

echo "Finished including base library"


echo "Running tests"
./compare/run_all.py tests/FastR/builtins/$1 -s -t "FastR $1 Tests" -d
