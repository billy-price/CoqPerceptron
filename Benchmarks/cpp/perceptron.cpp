/***************************************************************************************
    File: perceptron.cpp

    Description:
      Runs an arbitrary-precision rational valued perceptron algorithm.
      This program will infinite loop if the dataset is not linearly separable.
      Reads input from stdin and outputs to stdout.

    Input: a training set
    Example:

    2     // number of training vectors
    2     // number of features per vector
    1     // label 1
    1/2   // vector 1, feature 1
    1.2   // vector 1, feature 2
    0     // label 2
    0     // vector 2, feature 1
    1%3   // vector 2, feature 2

    resulting in the following vectors:
      <1 % 1, 1 % 2, 6 % 5> and <-1 % 1, 0 % 1, 1 % 3>
      // both % & / can be used as fraction.
      // labels are transformed from {0, 1} to {-1, 1} and appended to front of vectors.

    Output:
      This program will either infinite loop or termintate after outputing a weight
      vector representing the hyperplane sperating the data (1 feature per line).

    Example output (for the above example input).
    -1 % 1
    1 % 1
    7 % 5

    which represents the following 2D line.
    y = -7/5x - 1/||<1 % 1, 7 % 5>||
 ***************************************************************************************/
#include <iostream>
#include <string>
#include <vector>
#include <limits>

#include <boost/rational.hpp>
#include <boost/multiprecision/gmp.hpp>

typedef boost::multiprecision::mpz_int Z;
typedef boost::rational<Z> Q;
typedef std::vector<Q> Qvec;

std::istream& operator >> (std::istream& ins, Q& q);
std::ostream& operator << (std::ostream& outs, const Q& q);

// Vector Operations
Q dot (const Qvec& x, const Qvec& y);
Qvec add (const Qvec& x, const Qvec& y);
Qvec mult (const Qvec& x, const Q q);
inline int sign(Q q) { return (0 < q) - (0 > q); } // 1 or -1

Qvec perceptron(const std::vector<Qvec>& features, const std::vector<int>& labels);

int main(int argc, char ** argv){
  std::size_t nvecs, nfeats;
  std::cin >> nvecs >> nfeats;

  std::vector<Qvec> vecs;
  std::vector<int>  lbls;

  for (std::size_t i = 0; i < nvecs; ++i){
    int lbl;
    std::cin >> lbl;
    lbls.push_back(lbl*2-1); //{0,1} => {-1, 1}

    std::cin.ignore(std::numeric_limits<int>::max(),'\n'); //ignore until new line

    Qvec vec(1, Q(1, 1));
    for (std::size_t j = 0; j < nfeats; ++j){
      Q q;
      std::cin >> q;
      vec.push_back(q);
    }
    vecs.push_back(vec);
  }

  Qvec w = perceptron(vecs, lbls);

  if (argc != 1){ // pretty print
    std::cout << "<";
    for (std::size_t i = 0; i < w.size(); ++i){
      std::cout << w[i];
      if (i != w.size() - 1){
        std::cout << ", ";
      }
    }
    std::cout << ">" << std::endl;
  } else {
    for (std::size_t i = 0; i < w.size(); ++i){
      std::cout << w[i] << std::endl;
    }
  }
  return 0;
}

// for now, we assume each number is on it's own line
std::istream& operator >> (std::istream& ins, Q& q){
  Z n, d;
  char c;

  std::string num;

  getline(ins, num);

  std::size_t pos;
  if ((pos = num.find('%')) != std::string::npos ||
      (pos = num.find('/')) != std::string::npos){  // fractional
    n = Z(num.substr(0, pos));
    d = Z(num.substr(pos+1));
  } else if ((pos = num.find('.')) != std::string::npos){ // floating point
    std::string N, D;
    N = num.substr(0, pos);
    D = num.substr(pos+1);
    d = 1;
    for (std::size_t i = 0; i < D.length(); ++i){ // pow doesn't work (it has limited precision)
      d *= 10;
    }
    n = Z(N)*d + Z(D);
  } else { // integral
    n = Z(num);
    d = 1;
  }

  q = Q(n, d);

  return ins;
}

std::ostream& operator << (std::ostream& outs, const Q& q){
  return outs << q.numerator() << " % " << q.denominator();
}

Q dot (const Qvec& x, const Qvec& y){
  Q res(0, 1);
  for (std::size_t i = 0; i < x.size(); ++i){
    res += x[i] * y[i];
  }
  return res;
}

Qvec add (const Qvec& x, const Qvec& y){
  Qvec res(x.size());
  for (std::size_t i = 0; i < x.size(); ++i){
    res[i] = x[i] + y[i];
  }
  return res;
}

Qvec mult (const Qvec& x, const Q q){
  Qvec res(x.size());
  for (std::size_t i = 0; i < x.size(); ++i){
    res[i] = x[i] * q;
  }
  return res;
}

Qvec perceptron(const std::vector<Qvec>& features, const std::vector<int>& labels){
  Qvec weights(features[0].size(), Q(0, 1));

  size_t fuel = 0;
  bool converged;
  do {
    ++fuel;
    converged = true;

    for (std::size_t i = 0; i < features.size(); ++i){
      Q res = dot(weights, features[i]);

      if (sign(res) != labels[i] || res == Q(0,1)) { // wrong sign or res = 0.
        weights = add(weights, mult(features[i], Q(labels[i], 1)));
        converged = false;
      }
    }
  } while (!converged);
  std::cerr << "Fuel: " << fuel << std::endl;
  return weights;
}
