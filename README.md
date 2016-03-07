# CoqPerceptron
Verified Coq Implementation of the Integer Valued Perceptron Algorithm

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
Due to the scaling of this dataset by 10,000 it is suggested to change the bias term
to 10,000. This drastically changes the number of Epochs (iterations) of the perceptron.

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

Don't Forget to change this back when you want to run this on the other benchmarks.
