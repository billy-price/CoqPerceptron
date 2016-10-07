# -*- coding: utf-8 -*-
from matplotlib import use
use('Agg')

import matplotlib.pyplot as plot
import numpy as np

plot.rcParams.update({'font.size': 16.1})

def plot_data(img_name, file_name, xlabel, yRange = None):
  figure = plot.figure()
  axis = figure.add_subplot(1, 1, 1)

  A = []
  B = []
  C = []
  E = []
  N = [""]

  F = open(file_name, 'r')

  for l in F.readlines():
    data = l.split()
    N.append(data[0])
    A.append(float(data[8]))
    B.append(float(data[2]))
    C.append(float(data[5]))
    E.append(float(data[11]))
  F.close()

  X = np.arange(len(A))

  D = [x + y for (x, y) in zip(B, C)]
  A = [x / y for (x, y) in zip(A, D)]
  B = [x / y for (x, y) in zip(B, D)]
  C = [x / y for (x, y) in zip(C, D)]
  E = [x / y for (x, y) in zip(E, D)]

  a_bar = plot.bar(X-0.375, A, color = '#00fa9a', width = 0.25, hatch='//')
  b_bar = plot.bar(X-0.125, B, color = 'cyan',width = 0.25, hatch='xx')
  c_bar = plot.bar(X-0.125, C, color = '#ee82ee', bottom = B, width = 0.25, hatch='*')
  e_bar = plot.bar(X+0.125, E, color = 'orange', width = 0.25)

  axis.axes.get_xaxis().set_ticklabels(N)

  if yRange:
    plot.ylim(yRange)
  figure.canvas.draw()
  axis.axes.get_yaxis().set_ticklabels(
       [x.get_text()+'x' for x in axis.get_yticklabels()])

  plot.legend([a_bar, b_bar, c_bar, e_bar],
              ["Coq Perceptron", "C++ Perceptron", "Coq Validator", "CoqOpt"],
              loc="upper center", bbox_to_anchor=(0.5, 1.125), ncol=2)
  plot.xlabel(xlabel)
  plot.ylabel("Time")
  plot.savefig(img_name)

plot_data("images/VectorsPlot.png", "vectors.plot", "Number of Vectors", [0,9])
plot_data("images/FeaturePlot.png", "features.plot", "Number of Features", [0,3])
plot_data("images/ZPlot.png", "Z.plot", u'Precision Bound -- Q = a/Z, a ∈ [-Z, Z]', [0,3])
