# CoqPerceptron
Verified Coq Implementation of the Integer-Valued Perceptron Algorithm

# Key Files

## Coq
* [ZvecArith.v](https://github.com/tm507211/CoqPerceptron/blob/master/ZvecArith.v): vector arithmetic
* [PerceptronDef.v](https://github.com/tm507211/CoqPerceptron/blob/master/PerceptronDef.v): Coq Perceptron
* [PerceptronSound.v](https://github.com/tm507211/CoqPerceptron/blob/master/PerceptronSound.v): soundness
* [TerminationRefinement.v](https://github.com/tm507211/CoqPerceptron/blob/master/TerminationRefinement.v): termination refinement proofs
* [MCEBounds.v](https://github.com/tm507211/CoqPerceptron/blob/master/MCEBounds.v): the "AC bounds" lemmas
* [PerceptronConvergence.v](https://github.com/tm507211/CoqPerceptron/blob/master/PerceptronConvergence.v): convergence proof
* [fuel.v](https://github.com/tm507211/CoqPerceptron/blob/master/fuel.v): fuel monad
* [fueled_perceptron.v](https://github.com/tm507211/CoqPerceptron/blob/master/fueled_perceptron.v): fueled Perceptron and extraction

## Benchmarks/
* [cpp/](https://github.com/tm507211/CoqPerceptron/tree/master/Benchmarks/cpp): C++ implementation of Perceptron; also, program to generate random data sets
* [data/](https://github.com/tm507211/CoqPerceptron/tree/master/Benchmarks/data): Real-world and randomly-generated data sets
* [scripts/](https://github.com/tm507211/CoqPerceptron/tree/master/Benchmarks/scripts): Scripts for generated random data sets and running benchmarks

# Building the Coq Development

Just type

```Bash
make
```

## Prerequisites 

* Coq 8.4pl6
* GHC 7.10.2

Our development may compile with other versions, but this 
hasn't been tested.

The unoptimized extraction into Haskell of Perceptron does not 
compile in GHC 7.10.2 without a small tweak, to move the type declaration generated 
for `unsafeCoerce` to after a compiler-specific `#ifdef` at the top of 
the file. We automate a patch that does this fix in the `Makefile`.

Our optimized extracted Perceptron didn't trigger this extraction 
bug.

# Building Benchmarks

## Build Plots

Using make in the Benchmarks directory will extract, compile, and run all benchmarks on the
provided data.

```Bash
cd Benchmarks && make
```

If you'd prefer to just make the plots, you can use the following commands, to have make
avoid rerunning the benchmarks and use the output already provided.

```Bash
cd Benchmarks/cpp && make perceptron
cd Benchmarks/hs && make
touch Benchmarks/output/*
cd Benchmarks && make
```

## Running Benchmarks

If you want to rerun any or all of the benchmarks you can use the following commands

```Bash
# Randomly Generated Data Sets
cd Benchmarks && make benchmarks	# Run all three benchmarks on provided data
cd Benchmarks && make cppbench		# Run just the C++ benchmarks
cd Benchmarks && make hsbench		# Run just Coq => Haskell Extraction
cd Benchmarks && make hsoptbench	# Run just Coq =>opt Haskell Extraction

# Real World Data Sets
cd Benchmarks && make iris		# Run on Iris Data Set
cd Benchmarks && make rocks		# Run on Rocks and Mines Data Set
```

Running make again in the Benchmarks directory will update the plots with your new
benchmark data.

```Bash
cd Benchmarks && make
```

## Real World Data Sets

Both the Iris Data Set and Rocks and Mines data sets are from the UCI Machine Learning
Data Repository. They files have been modified to fit the input description in data/ and
scaled to make each feature an integral value. Iris Dataset is scaled by 10, and Rocks and
mines by 10,000.

Iris Dataset is available [here.](https://archive.ics.uci.edu/ml/datasets/Iris)
Rocks and Mines is available [here.](https://archive.ics.uci.edu/ml/datasets/Connectionist+Bench+%28Sonar,+Mines+vs.+Rocks%29)

### Rocks and Mines Dataset
Due to the scaling of this dataset by 10,000, we suggest that you change the bias term
to 10,000 (as we describe in the paper). 
This drastically changes the number of Epochs (iterations) required for convergence, in both 
the C++ and Coq versions of Perceptron.

On line 99 of Benchmarks/cpp/perceptron.cpp change
```C++
    features[i][0] = 1; //** Bias
```
to
```C++
    features[i][0] = 10000; //*** Bias
```

On line 2135 of Benchmarks/hs/FueledPerceptron.hs change the definition of consb
```Haskell
  Cons0 (Zpos XH) n v
```
to
```Haskell
  Cons0 (Zpos (XO (XO (XO (XO (XI (XO (XO (XO (XI (XI (XI (XO (XO XH)))))))))))))) n v
```

and On line 3324 of Benchmarks/hs/FueledPerceptronOpt.hs change the definition of consb
```Haskell
  (\a _ v -> a : v) ( 1) n v
```
to
```Haskell
  (\a _ v -> a : v) ( 10000) n v
```

Don't forget to revert this change before running the other benchmarks.
