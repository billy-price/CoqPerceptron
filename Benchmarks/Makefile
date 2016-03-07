SHELL := /bin/bash

plot_imgs = \
	plots/images/EpochPlot.png \
	plots/images/FeaturePlot.png \
	plots/images/VectorsPlot.png \
	plots/images/ZPlot.png
plot_files = \
	plots/features.plot \
	plots/vectors.plot \
	plots/Z.plot

plots: $(plot_imgs)

$(plot_imgs) :  $(plot_files) plots/makeplots.gplot
	cd plots && gnuplot makeplots.gplot

$(plot_files) : cpp/makeplotfiles output/fuels output/cpptimes output/hstimes output/hsopttimes
	cpp/makeplotfiles

cpp/makeplotfiles : cpp/makeplotfiles.cpp
	cd cpp && make makeplotfiles

benchmarks : cppbench hsbench hsoptbench

iris: scripts/runbenchmarks.sh cpp/perceptron hs/ReadData hs/ReadDataOpt
	@TIMEFORMAT="C++    : %lR"; time cpp/perceptron < data/iris_data
	@TIMEFORMAT="Coq    : %lR"; time hs/ReadData < data/iris_data > /dev/null
	@TIMEFORMAT="CoqOpt : %lR"; time hs/ReadDataOpt < data/iris_data > /dev/null

rocks: scripts/runbenchmarks.sh cpp/perceptron hs/ReadData hs/ReadDataOpt
	@TIMEFORMAT="C++    : %lR"; time cpp/perceptron < data/rocks_int.dat
	@TIMEFORMAT="Coq    : %lR"; time hs/ReadData < data/rocks_int.dat > /dev/null
	@TIMEFORMAT="CoqOpt : %lR"; time hs/ReadDataOpt < data/rocks_int.dat > /dev/null

cppbench output/fuels output/cpptimes: scripts/runbenchmarks.sh cpp/perceptron
	scripts/runbenchmarks.sh cpp/perceptron data/ --all_vectors > output/fuels 2> output/cpptimes

cpp/perceptron:
	cd cpp && make perceptron

hsbench output/hstimes: scripts/runbenchmarks.sh hs/ReadData
	scripts/runbenchmarks.sh hs/ReadData data/ > /dev/null 2> output/hstimes

hs/ReadData:
	cd hs && make ReadData

hsoptbench output/hsopttimes: scripts/runbenchmarks.sh hs/ReadDataOpt
	scripts/runbenchmarks.sh hs/ReadDataOpt data/ --all_vectors > /dev/null 2> output/hsopttimes

hs/ReadDataOpt:
	cd hs && make ReadDataOpt

