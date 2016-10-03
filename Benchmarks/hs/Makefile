all: RunPerceptron RunValidator

RunPerceptron: RunPerceptron.hs ReadData.hs Perceptron.hs
	ghc RunPerceptron.hs

RunValidator: RunValidator.hs ReadData.hs Perceptron.hs
	ghc RunValidator.hs

clean:
	rm -f *.hi *.o RunPerceptron RunValidator
