//********************************
//** File: perceptron.cpp
//**
//** Description:
//**   Executes perceptron algorithm on
//**   provided dataset and prints the
//**   total fuel required to converge.
//**   If the dataset is not linearly
//**   separable, then the code will
//**   get stuck in an infinite loop.
//**
//** Usage:
//**
//** $ ./perceptron < <FEATURES_FILE>
//**
//*********************************
#include <iostream>
#include <vector>

typedef long long ptype;

//*************** VECTOR FUNCTIONS *****************
ptype dot(const std::vector<ptype>& x,
          const std::vector<ptype>& y) {

  ptype result = 0;
  for (size_t i = 0; i < x.size(); ++i)
    result += x[i] * y[i];

  return result;
}

const std::vector<ptype> add(const std::vector<ptype>& x,
                             const std::vector<ptype>& y) {

  std::vector<ptype> result(x.size());
  for (size_t i = 0; i < x.size(); ++i)
    result[i] = x[i] + y[i];

  return result;
}

const std::vector<ptype> mult(const std::vector<ptype>& x, int a) {

  std::vector<ptype> result(x.size());
  for (size_t i = 0; i < x.size(); ++i)
    result[i] = x[i] * a;

  return result;
}
//***************************************************

//************* PERCEPTRON FUNCTIONS ****************
inline int sign(ptype a) {
  return (0 < a) - (0 > a);
}

size_t perceptron(const std::vector<std::vector<ptype> >& features,
                  const std::vector<int>& labels) {

  std::vector<ptype> weights(features[0].size());

  size_t fuel = 0;
  bool converged;
  do {
    fuel++;
    converged = true;

    for(size_t i = 0; i < features.size(); ++i) { 
      int y = sign(dot(weights, features[i]));

      if (y != labels[i]) {
        weights = add(weights, mult(features[i], labels[i]));
        converged = false;
      }
    } 

  } while (!converged);

  return fuel;
}
//***************************************************

int main(int argc, char** argv) {
  //** Read feature vectors and labels
  int training_count, feature_count;
  std::cin >> training_count >> feature_count;
  ++feature_count; //** Account for bias

  std::vector<int> labels(training_count);
  std::vector<std::vector<ptype> > features(training_count);
  for (int i = 0; i < training_count; ++i)
    features[i].resize(feature_count);

  for (int i = 0; i < training_count; ++i) {
    std::cin >> labels[i];
    labels[i] = labels[i] ? 1 : -1;

    features[i][0] = 1; //** Bias
    for (int j = 1; j < feature_count; ++j)
      std::cin >> features[i][j];
  }

  std::cout << "Fuel: " << perceptron(features, labels) << std::endl;
}
