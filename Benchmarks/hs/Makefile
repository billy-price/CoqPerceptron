all: RunPerceptron RunValidator

addImportDataRatio:
	grep -q '^import Data.Ratio' Perceptron.hs || sed -i -f addImportDataRatio.sed Perceptron.hs

RunPerceptron: RunPerceptron.hs ReadData.hs Perceptron.hs addImportDataRatio
	ghc RunPerceptron.hs

RunValidator: RunValidator.hs ReadData.hs Perceptron.hs addImportDataRatio
	ghc RunValidator.hs

clean:
	rm -f *.hi *.o RunPerceptron RunValidator

.phony: addImportDataRatio
