all: Benchmarks/hs/FueledPerceptron.hs Benchmarks/hs/FueledPerceptronOpt.hs

Benchmarks/hs/FueledPerceptron.hs Benchmarks/hs/FueledPerceptronOpt.hs: fueled_perceptron.vo

fueled_perceptron.vo: fueled_perceptron.v perceptron.vo fuel.vo
	coqc fueled_perceptron.v

perceptron.vo: perceptron.v
	coqc perceptron.v

fuel.vo: fuel.v
	coqc fuel.v

clean:
	rm -f *.vo *.glob *.ml *.mli
