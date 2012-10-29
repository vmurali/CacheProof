#!/bin/sh

dirs="BT CG DC FT IS LU MG SP"
export OMP_NUM_THREADS=$1
for dir in $dirs; do
  cd $dir
  ../a.out > $2 &
  cd ..
done

