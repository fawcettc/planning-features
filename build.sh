#!/bin/bash

cd fast-downward
./build_all
cd ../

cd lpg
make
cd ../

cd runsolver
make
cd ../

cd sat/madagascar
make
cd ../../

cd torchlight
make
cd ../
