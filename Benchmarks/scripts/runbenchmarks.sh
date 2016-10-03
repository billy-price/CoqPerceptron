#!/bin/bash

if [ -z "$1" ] || [ -z "$2" ] || [ -z "$3" ] || ([ -n "$5" ] && [ -z "$6" ])
then
  this=`basename "$0"`
  echo "Usage: $this <PROGRAM_TO_RUN> <PATH_TO_DATA> <PATH_TO_OUTPUT> [<FUEL_OUTPUT>] [<VALIDATOR> <VALIDATION_OUTPUT>]"
  echo "Example: $this cpp/perceptron data/ output/cpp/ output/fuels hs/RunValidator output/cpp_valid.dat"
  exit 1
fi

if [ -z "$4" ]
then
  fout="/dev/null"
else
  fout="$4"
fi

vec=(50 100 200 400 800 1600 3200)
feat=(100 200 400 800 1600 3200)
Z=(100 200 400 800 1600 3200 6400 12800)

for i in ${vec[*]};
do
  echo "vectors $i" >> "$fout"
  echo "vectors $i"
  if [ -n "$5" ]
  then
    echo "vectors $i" >&2
    echo "vectors $i" >> "$6"
  fi
  for j in `seq 1 10`;
  do
    TIMEFORMAT="%lR"; time ($1 < $2/vec${i}_$j.dat > ${3}/vec${i}_$j 2>> "$fout") 2>&1
    if [ -n "$5" ]
    then
      TIMEFORMAT="%lR"; time (cat $2/vec${i}_$j.dat ${3}/vec${i}_$j | $5 >> "$6")
    fi
  done
done

for i in ${feat[*]};
do
  echo "features $i" >> "$fout"
  echo "features $i"
  if [ -n "$5" ]
  then
    echo "features $i" >&2
    echo "features $i" >> "$6"
  fi
  for j in `seq 1 10`;
  do
    TIMEFORMAT="%lR"; time ($1 < $2/feat${i}_$j.dat > ${3}/feat${i}_$j 2>> "$fout") 2>&1
    if [ -n "$5" ]
    then
      TIMEFORMAT="%lR"; time (cat $2/feat${i}_$j.dat ${3}/feat${i}_$j | $5 >> "$6")
    fi
  done
done

for i in ${Z[*]};
do
  echo "Z $i" >> "$fout"
  echo "Z $i"
  if [ -n "$5" ]
  then
    echo "Z $i" >&2
    echo "Z $i" >> "$6"
  fi
  for j in `seq 1 10`;
  do
    TIMEFORMAT="%lR"; time ($1 < $2/Z${i}_$j.dat > ${3}/Z${i}_$j 2>> "$fout") 2>&1
    if [ -n "$5" ]
    then
      TIMEFORMAT="%lR"; time (cat $2/Z${i}_$j.dat ${3}/Z${i}_$j | $5 >> "$6")
    fi
  done
done
