# CoqPerceptron
Verified Coq Implementation of the Rational-Valued Perceptron Algorithm

# Key Files

## Coq
* [QvecArith.v](https://github.com/tm507211/CoqPerceptron/blob/master/QvecArith.v): vector arithmetic
* [PerceptronDef.v](https://github.com/tm507211/CoqPerceptron/blob/master/PerceptronDef.v): Coq Perceptron
* [PerceptronSound.v](https://github.com/tm507211/CoqPerceptron/blob/master/PerceptronSound.v): soundness
* [TerminationRefinement.v](https://github.com/tm507211/CoqPerceptron/blob/master/TerminationRefinement.v): termination refinement proofs
* [MCEBounds.v](https://github.com/tm507211/CoqPerceptron/blob/master/MCEBounds.v): the "AC bounds" lemmas
* [PerceptronConvergence.v](https://github.com/tm507211/CoqPerceptron/blob/master/PerceptronConvergence.v): convergence proof
* [extraction.v](https://github.com/tm507211/CoqPerceptron/blob/master/extraction.v): fueled Perceptron and extraction

## Benchmarks/
* [cpp/](https://github.com/tm507211/CoqPerceptron/tree/master/Benchmarks/cpp): C++ implementation of Perceptron; also, program to generate random data sets
* [hs/](https://github.com/tm507211/CoqPerceptron/tree/master/Benchmarks/hs):Extracted CoqPerceptron to Haskell
* [hsopt/](https://github.com/tm507211/CoqPerceptron/tree/master/Benchmarks/hsopt): Soundly Optimized Extraction of CoqPercepton to Haskell
* [data/](https://github.com/tm507211/CoqPerceptron/tree/master/Benchmarks/data): Real-world and randomly-generated data sets
* [output/](https://github.com/tm507211/CoqPerceptron/tree/master/Benchmarks/output):Output and timing results from running the CPP, HS, and HSOpt verions of the Perceptron.
* [scripts/](https://github.com/tm507211/CoqPerceptron/tree/master/Benchmarks/scripts): Scripts for generated random data sets and running benchmarks

# Building the Coq Development

Simply type

```Bash
make
```

## Prerequisites 

### For building CoqPerceptron and C++ Perceptron Implementations
* Coq 8.5pl2
* GHC 7.6.3
* G++ 4.8.4
* Boost 1.54

### For creating the plotting files
* Python 2.7.6
* matplotlib 1.3.1
* gnuplot 4.6.4

Our development may compile with other versions, but this 
hasn't been tested.

# Building CoqPerceptron (Benchmarks/hs/)

```Bash
  cd Benchmarks/hs
  make
```

# Building Optimized CoqPerceptron (Benchmarks/hsopt)

```Bash
  cd Benchmarks/hsopt
  make
```

# Building C++ Perceptron Implementation (Benchmarks/cpp)

```Bash
  cd Benchmarks/cpp
  make
```

# Running Benchmarks

## Generating new DataSets

Note: This will overwrite the data in [data/](https://github.com/tm507211/CoqPerceptron/tree/master/Benchmarks/data)

```Bash
  cd Benchmarks
  scripts/gen_data.sh
```

## Run each Perceptron implementation on the generated data

```Bash
  scripts/runbenchmarks.sh cpp/perceptron data/ output/cpp output/fuels hs/RunValidator output/cpp_valid.dat > output/cpptimes 2> output/cpp_validtimes
  scripts/runbenchmarks.sh hs/RunPerceptron data/ output/hs > output/hstimes
  scripts/runbenchmarks.sh hsopt/RunPerceptron data/ output/hsopt > output/hsopttimes
```
Note: You may wish to put this in a script and run that as each command may
take a considerable amount of time to run

## Creating Plot Files

```Bash
  cpp/makeplotfiles
  cd plots
  python makeplots.py
  gnuplot epochs.gplot
```

