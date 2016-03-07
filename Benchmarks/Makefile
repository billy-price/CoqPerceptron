plot_imgs = \
	plots/images/EpochPlot.png \
	plots/images/FeaturePlot.png \
	plots/images/VectorsPlot.png \
	plots/images/ZPlot.png
plot_files = \
	plots/features.plot \
	plots/vectors.plot \
	plots/Z.plot
outputs = \
	output/fuels \
        output/cpptimes \
	output/hstimes \
	output/hsopttimes

plots: $(plot_imgs)

$(plot_imgs) :  $(plot_files) plots/makeplots.gplot
	cd plots && gnuplot makeplots.gplot

$(plot_files) : cpp/makeplotfiles benchmarks
	cpp/makeplotfiles

cpp/makeplotfiles : cpp/makeplotfiles.cpp
	cd cpp && make makeplotfiles

benchmarks : $(outputs)

$(outputs) : scripts/runbenchmarks.sh
	cd cpp && make perceptron
	cd hs && make
	scripts/runbenchmarks.sh cpp/perceptron data/ --all_vectors > output/fuels 2> output/cpptimes
	scripts/runbenchmarks.sh hs/ReadData data/ > /dev/null 2> output/hstimes
	scripts/runbenchmarks.sh hs/ReadDataOpt data/ --all_vectors > /dev/null 2> output/hsopttimes
