//********************************
//** File: data_generator.cpp
//**
//** Description:
//**   Produce a linearly separable dataset
//**   from a weight vector with randomly
//**   generated weights.
//**
//** Usage:
//** $ ./data_generator
//**   -o <OUTPUT_FILE>
//**   -t <TRAINING_COUNT>
//**   -f <FEATURE_COUNT>
//**   -b <BOUND>
//**
//*********************************
#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <random>
#include <algorithm>

typedef long long ptype;

class Random {
  public:
    Random(ptype b) : bound(b), engine(std::random_device{}()) {}

    ptype operator()() {
      return std::uniform_int_distribution<ptype>{-bound, bound}(engine);
    }

  private:
    ptype bound;
    std::default_random_engine engine;
};

int main(int argc, char** argv) {
  if (!(argc % 2)) {
    std::cout << "** Invalid number of arguments" << std::endl;
    return 0;
  }

  //** Default parameter values
  std::string file_string = "test_features.dat";
  int training_count = 100;
  int feature_count = 10;
  int bound = 100;
  //**


  //** Command line parsing
  for (size_t i = 1; i < argc; i += 2) {
    std::stringstream argss(std::string(argv[i]) + " " + std::string(argv[i+1]));
    std::string option;
    argss >> option;

    if (option == "-o") {
      argss >> file_string;

    } else if (option == "-t") {
      if (!(argss >> training_count) || training_count < 2) {
        std::cout << "** Invalid training count" << std::endl;
        return 0;
      }

    } else if (option == "-f") {
      if (!(argss >> feature_count) || feature_count < 1) {
        std::cout << "** Invalid feature size" << std::endl;
        return 0;
      }

    } else if (option == "-b") {
      if (!(argss >> bound) || bound < 1) {
        std::cout << "** Invalid bound" << std::endl;
        return 0;
      }

    } else {
      std::cout << "** Invalid option: " << option << std::endl;
      return 0;
    }
  }

  std::ofstream features_ofs(file_string);
  if (!features_ofs.is_open()) {
    std::cout << "** Invalid output file: " << file_string << std::endl;
    return 0;
  }
  //**

  //** Generate features
  std::vector<ptype> weights(feature_count + 1); //** Add bias
  std::vector<ptype> features(feature_count);

  std::generate(weights.begin(), weights.end(), Random(bound));

  features_ofs << training_count << std::endl;
  features_ofs << feature_count << std::endl;
  while (training_count--) {
    ptype dot;
    do {
      dot = weights[0];
      std::generate(features.begin(), features.end(), Random(bound));
      for (size_t i = 0; i < features.size(); ++i)
        dot += weights[i+1] * features[i];
    } while (!dot); //** Check if point lies on boundary

    features_ofs << (dot > 0) << std::endl;
    for (size_t i = 0; i < features.size(); ++i)
      features_ofs << features[i] << std::endl;
  }
}
