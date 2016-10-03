#!/bin/bash

vec=(50 100 200 400 800 1600 3200)
feat=(100 200 400 800 1600 3200)
Z=(100 200 400 800 1600 3200 6400 12800)

base_dir="$(dirname "$0")/../"

for i in ${vec[*]};
do
  echo "vectors $i"
  for j in `seq 1 10`;
  do
    ${base_dir}cpp/data_generator -o ${base_dir}data/vec${i}_$j.dat -t $i -f 1000 -b 250
  done
done

for i in ${feat[*]};
do
  echo "features $i"
  for j in `seq 1 10`;
  do
    ${base_dir}cpp/data_generator -o ${base_dir}data/feat${i}_$j.dat -t 100 -f $i -b 250
  done
done

for i in ${Z[*]};
do
  echo "Z $i"
  for j in `seq 1 10`;
  do
    ${base_dir}cpp/data_generator -o ${base_dir}data/Z${i}_$j.dat -t 100 -f 1000 -b $i
  done
done
