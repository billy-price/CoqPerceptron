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
        output/times \
bin = \
	cpp/perceptron \
	hs/ReadData \
	hs/ReadDataOpt

plots: $(plot_imgs)

$(plot_imgs) :  $(plot_files) plots/makeplots.gplot
	cd plots && gnuplot makeplots.gplot

$(plot_files) : cpp/makeplotfiles benchmarks
	cpp/makeplotfiles

cpp/makeplotfiles : cpp/makeplotfiles.cc
	cd cpp && make makeplotfiles

benchmarks : $(outputs)

$(outputs) : scripts/runbenchmarks.sh $(bin)
	scripts/runbenchmarks.sh cpp/perceptron data/ --all_vectors
	scripts/runbenchmarks.sh hs/ReadData data/
	scripts/runbenchmarks.sh hs/ReadDataOpt data/ --all_vectors

cpp/perceptron : cpp/perceptron.cpp
	cd cpp && make perceptron

hs/ReadData : hs/ReadData.hs hs/FeuledPerceptron.hs
	cd hs && make ReadData

hs/ReadDataOpt : hs/ReadDataOpt.hs hs/FeuledPerceptronOpt.hs
	cd hs && make ReadDataOpt

hs/FeuledPerceptron.hs hs/FeuledPerceptronOpt.hs:
	cd .. && make
