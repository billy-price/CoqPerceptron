#!/bin/bash

if [ -z "$1" ] || [ -z "$2" ]
then
  this=`basename "$0"`
  echo "Usage: $this <PROGRAM_TO_RUN> <PATH_TO_DATA> [--all_vectors]"
  echo "Example: $this cpp/perceptron data/ --all_vectors"
  exit 1
fi

if [ -z "$3" ]
then
  vec=(50 100 200 400 800 1600)
else
  if [ "$3" == "--all_vectors" ]
  then
    vec=(50 100 200 400 800 1600 3200 6400 12800)
  fi
fi

feat=(100 200 400 800 1600 3200)
Z=(100 200 400 800 1600 3200 6400 12800)

for i in ${vec[*]};
do
  echo "vectors $i" >&2
  echo "vectors $i"
  for j in `seq 1 10`;
  do
    TIMEFORMAT="%lR"; time $1 < $2/vec${i}_$j.dat
  done
done

for i in ${feat[*]};
do
  echo "features $i" >&2
  echo "features $i"
  for j in `seq 1 10`;
  do
    TIMEFORMAT="%lR"; time $1 < $2/feat${i}_$j.dat
  done
done

for i in ${Z[*]};
do
  echo "Z $i" >&2
  echo "Z $i"
  for j in `seq 1 10`;
  do
    TIMEFORMAT="%lR"; time $1 < $2/Z${i}_$j.dat
  done
done
