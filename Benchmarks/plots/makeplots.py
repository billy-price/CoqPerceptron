# -*- coding: utf-8 -*-
import matplotlib.pyplot as plot
import numpy as np

def plot_data(img_name, file_name, xlabel, yRange = None):
  figure = plot.figure()
  axis = figure.add_subplot(1, 1, 1)

  A = []
  B = []
  C = []
  N = [""]

  F = open(file_name, 'r')

  for l in F.readlines():
    data = l.split()
    N.append(data[0])
    A.append(float(data[8]))
    B.append(float(data[2]))
    C.append(float(data[5]))
  F.close()

  X = np.arange(len(A))

  D = [x + y for (x, y) in zip(B, C)]
  A = [x / y for (x, y) in zip(A, D)]
  B = [x / y for (x, y) in zip(B, D)]
  C = [x / y for (x, y) in zip(C, D)]

  a_bar = plot.bar(X-0.33, A, color = 'g', width = 0.33)
  b_bar = plot.bar(X, B, color = 'b',width = 0.33)
  c_bar = plot.bar(X, C, color = 'r', bottom = B, width = 0.33)

  axis.axes.get_xaxis().set_ticklabels(N)

  if yRange:
    plot.ylim(yRange)
  figure.canvas.draw()
  axis.axes.get_yaxis().set_ticklabels(
       [x.get_text()+'x' for x in axis.get_yticklabels()])

  plot.legend([a_bar, b_bar, c_bar],
              ["Coq Perceptron", "C++ Perceptron", "Coq Validator"],
              loc=0)
  plot.xlabel(xlabel)
  plot.ylabel("Time")
  plot.savefig(img_name)

plot_data("images/vecotrs.png", "vectors.plot", "Number of Vectors")
plot_data("images/features.png", "features.plot", "Number of Features")
plot_data("images/Z.png", "Z.plot", u'Precision Bound -- Q = a/Z, a ∈ [-Z, Z]', [0,3])
