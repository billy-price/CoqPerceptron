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
  F = []
  N = [""]

  file = open(file_name, 'r')

  for l in file.readlines():
    data = l.split()
    N.append(data[0])
    A.append(float(data[8]))
    B.append(float(data[2]))
    C.append(float(data[5]))
    E.append(float(data[11]))
    F.append(float(data[14]))
  file.close()

  X = np.arange(len(A))

  D = [x + y for (x, y) in zip(F, C)]
  A = [x / y for (x, y) in zip(A, D)]
  B = [x / y for (x, y) in zip(B, D)]
  C = [x / y for (x, y) in zip(C, D)]
  E = [x / y for (x, y) in zip(E, D)]
  F = [x / y for (x, y) in zip(F, D)]

  a_bar = plot.bar(X+0.3, A, color = '#00fa9a', width = 0.2, hatch='//')
  b_bar = plot.bar(X+0.1, B, color = 'cyan',width = 0.2, hatch='xx')
  c_bar = plot.bar(X-0.3, C, color = '#ee82ee', bottom = F, width = 0.2, hatch='*')
  e_bar = plot.bar(X-0.1, E, color = 'orange', width = 0.2)
  f_bar = plot.bar(X-0.3, F, color = '#ffff00', width=0.2, hatch='\\')

  axis.axes.get_xaxis().set_ticklabels(N)

  # set y-axis log scale, with labels at 10^0, 10^1, 10^2, 10^3
  y = np.array([1, 10, 100, 1000])
  axis.set_yscale('log')
  plot.yticks(y)
  
  if yRange:
    plot.ylim(yRange)
  figure.canvas.draw()

  axis.axes.get_yaxis().set_ticklabels(
       [x.get_text()+'x' for x in axis.get_yticklabels()])

  plot.legend([f_bar, c_bar, e_bar, b_bar, a_bar],
              ["C++ Float", "Validator",
               "Opt. Coq", "C++ Rational",
               "Vanilla Coq"],
              loc="upper center", bbox_to_anchor=(0.5, 1.125), ncol=2)
  plot.xlabel(xlabel)
  plot.ylabel("Time")
  plot.savefig(img_name)

plot_data("images/VectorsPlot.png", "vectors.plot", "Number of Vectors") # [0, 9]
plot_data("images/FeaturePlot.png", "features.plot", "Number of Features") # [0, 3]
plot_data("images/ZPlot.png", "Z.plot", u'Feature Coefficients q = a/Z, for a ∈ [-Z, Z]') #[0, 3]
