all: ReadData ReadDataOpt

ReadData: ReadData.hs FueledPerceptron.hs
	ghc ReadData.hs

ReadDataOpt: ReadDataOpt.hs FueledPerceptronOpt.hs
	ghc ReadDataOpt.hs

clean:
	rm -rf *.o *.hi ReadData ReadDataOpt
