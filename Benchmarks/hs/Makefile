all: ReadData ReadDataOpt

ReadData: ReadData.hs FueledPerceptron.hs
	ghc ReadData.hs

FueledPerceptron.hs:
	cd ../../ && make Benchmarks/hs/FueledPerceptron.hs

ReadDataOpt: ReadDataOpt.hs FueledPerceptronOpt.hs
	ghc ReadDataOpt.hs

FueledPerceptronOpt.hs:
	cd ../../ && make Benchmarks/hs/FueledPerceptronopt.hs

clean:
	rm -rf *.o *.hi ReadData ReadDataOpt
