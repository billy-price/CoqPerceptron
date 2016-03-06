all: Benchmarks/hs/FueledPerceptron.hs Benchmarks/hs/FueledPerceptronOpt.hs

Benchmarks/hs/FueledPerceptron.hs Benchmarks/hs/FueledPerceptronOpt.hs: fueled_perceptron.vo

# Hack to automatically fix a bug
fueled_perceptron.vo: fueled_perceptron.v perceptron.vo fuel.vo
	coqc fueled_perceptron.v
	head -8 Benchmarks/hs/FueledPerceptron.hs > out
	tail -n +10 Benchmarks/hs/FueledPerceptron.hs | head -8 >> out
	head -9 Benchmarks/hs/FueledPerceptron.hs | tail -1 >> out
	tail -n +18 Benchmarks/hs/FueledPerceptron.hs >> out
	mv out Benchmarks/hs/FueledPerceptron.hs

perceptron.vo: perceptron.v
	coqc perceptron.v

fuel.vo: fuel.v
	coqc fuel.v

clean:
	rm -f *.vo *.glob
