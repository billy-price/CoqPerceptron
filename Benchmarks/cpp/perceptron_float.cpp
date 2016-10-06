/**************************************************************************************
    File: perceptron.cpp

    Description:
      Runs a floating point (double) valued perceptron algorithm.
      This program may loop indefinately, if the data cannot be separated.
      Reads input from stdin and outputs to stdout

      For ease of use with the data provided with this repo,
      the input can be represented as integral, fractional, or fixed point number
      representations.

      The output will be in fixed point notation.
 **************************************************************************************/
#include <iostream>
#include <vector>
#include <string>
#include <cmath>
using namespace std;

inline double dot(const vector<double>& x, const vector<double>& y){
  double sum(0);
  for (size_t i = 0; i < x.size(); ++i){
    sum += x[i]*y[i];
  }
  return sum;
}

inline vector<double> add(const vector<double>& x, const vector<double>& y){
  vector<double> sum(x.size());
  for (size_t i = 0; i < x.size(); ++i){
    sum[i] = x[i] + y[i];
  }
  return sum;
}

inline vector<double> mult(const vector<double>& x, const double d){
  vector<double> prod = x;
  for (size_t i = 0; i < x.size(); ++i){
    prod[i] *= d;
  }
  return prod;
}

inline int sign(double d){ return (0 < d) - (0 > d); } // 1 or -1

vector<double> perceptron(const vector<vector<double> >& features, const vector<int>& labels){
  vector<double> weights(features[0].size(), 0);

  size_t fuel = 0;
  bool converged;
  do {
    ++fuel;
    converged = true;

    for (size_t i = 0; i < features.size(); ++i){
      double res = dot(weights, features[i]);

      if (sign(res) != labels[i] || res == 0){
        weights = add(weights, mult(features[i], labels[i]));
        converged = false;
      }
    }
  } while (!converged);
  std::cerr << "Fuel: " << fuel << endl;
  return weights;
}

double getNum(istream& ins){ // May result in over or underflow of the represented number
  long long int n, d;
  string num;

  getline(ins, num);
  size_t pos;
  if ((pos = num.find('%')) != string::npos ||
      (pos = num.find('/')) != string::npos){  //fractional  -- May Result in loss of precision !!!
    n = stoll(num.substr(0, pos));
    d = stoll(num.substr(pos+1));
  } else if ((pos=num.find(',')) != string::npos){ // fixed point
    std::string N, D;
    N = num.substr(0, pos);
    D = num.substr(pos+1);

    d = pow(10, D.length());
    n = stoll(N)*d + stoll(D);
  } else {
    n = stoll(num);
    d = 1;
  }
  return ((long double)n)/((long double)d);
}

int main(int argc, char ** argv){
  size_t nvecs, nfeats;
  cin >> nvecs >> nfeats;

  vector<vector<double> > vecs;
  vector<int> lbls;

  for(size_t i = 0; i < nvecs; ++i){
    int lbl;
    cin >> lbl;
    lbls.push_back(lbl*2-1.0); //{0,1} => {-1, 1}

    cin.ignore(numeric_limits<int>::max(), '\n');

    vector<double> vec(1, 1);
    for(size_t j = 0; j < nfeats; ++j){
      vec.push_back(getNum(cin));
    }
    vecs.push_back(vec);
  }
  vector<double> w = perceptron(vecs, lbls);

  for (size_t i = 0; i < w.size(); ++i){
    cout << w[i] << endl;
  }
  return 0;
}
