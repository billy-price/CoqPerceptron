/***************************************************************************************
    File: data_generator.cpp

    Description:
      produces a linearly separable dataset from a weight vector with randomly
      generated weights. All features will be uniformally drawn from [-1, 1]
      as bounded rationals.
      I.e if the bound for the dataset is 100 the denominator is set to 100 and
      the numerator is randomly chosen from [-100, 100] (integral values).

    Usage:
    data_generator
      -o <OUTPUT_FILE>
      -t <TRAINING_COUNT>
      -f <FEATURE_COUNT>
      -b <BOUND>
      -w (STDOUT | FEATURE | BOTH) // prints weights to stdout or at end of features_file
 ***************************************************************************************/
#include <iostream>
#include <fstream>
#include <vector>
#include <random>
#include <algorithm>
#include <string>
#include <sstream>

#include <boost/rational.hpp>
#include <boost/multiprecision/gmp.hpp>
#include <boost/multiprecision/random.hpp>

typedef boost::multiprecision::mpz_int Z;
typedef boost::rational<Z> Q;
typedef std::vector<Q> Qvec;

std::ostream& operator << (std::ostream& outs, const Q& q){
  return outs << q.numerator() << " % " << q.denominator();
}

class Random{
  public:
    Random (Z b) : bound(b), engine(std::random_device{}()) {}

    Q operator()() {
      return Q(randZ(), bound);
    }

  private:
    Z bound;
    std::mt19937 engine;

    Z randZ(){
      return boost::random::uniform_int_distribution<Z>(-bound, bound)(engine);
    }
};


int main(int argc, char ** argv){
  if (!(argc % 2) || argc > 11){
    std::cerr << "\033[1;31mError: Invalid number of Arguments.\n\033[0m";
    return -1;
  }

  std::string file_string = "test_features.dat";
  size_t training_count = 100;
  size_t feature_count = 10;
  char show_weight = 0; // 0 = don't print, 1 = std_out, 2 = features_file
  Z bound = 100;

  for (size_t i = 1; i < argc; i += 2){
    std::stringstream argss(std::string(argv[i]) + " " + std::string(argv[i+1]));
    std::string option;
    argss >> option;

    if (option == "-o"){
      argss >> file_string;

    } else if (option == "-t"){
      if (!(argss >> training_count) || training_count < 2) {
        std::cerr << "\033[1;31mError: Invalid training count.\n\033[0m";
        return -1;
      }

    } else if (option == "-f"){
      if (!(argss >> feature_count) || feature_count < 1) {
        std::cerr << "\033[1;31mError: Invalid feature count.\n\033[0m";
        return -1;
      }

    } else if (option == "-b"){
      if (!(argss >> bound) || bound < 1) {
        std::cerr << "\033[1;31mError: Invalid feature count.\n\033[0m";
        return -1;
      }

    } else if (option == "-w"){
      std::string w;
      argss >> w;
      if (w == "STDOUT"){
        show_weight = 1;
      } else if (w == "BOTH"){
        show_weight = 2;
      } else if (w == "FEATURE"){
        show_weight = 3;
      } else {
        std::cerr << "\033[1;31mError: Invalid selection: " << w << ".\n\033[0m";
        return -1;
      }

    } else {
      std::cerr << "\033[1;31mError: Invalid option: " << option << ".\n\033[0m";
      return -1;
    }
  }

  std::ofstream features_ofs(file_string);
  if (!features_ofs.is_open()) {
    std::cerr << "\033[1;31mError: Invalid Output file: " << file_string << ".\n\033[0m";
    return -1;
  }

  Qvec weights(feature_count + 1); // Adds bias term
  Qvec features(feature_count);

  std::generate(weights.begin(), weights.end(), Random(bound));

  features_ofs << training_count << std::endl;
  features_ofs << feature_count << std::endl;

  while (training_count--){
    Q dot;
    do {
      dot = weights[0];
      std::generate(features.begin(), features.end(), Random(bound));
      for (size_t i = 0; i < features.size(); ++i){
        dot += weights[i+1] * features[i];
      }
    } while (!dot); // make sure point does not lie on boundary

    features_ofs << (dot > 0) << std::endl;
    for (size_t i = 0; i < features.size(); ++i){
      features_ofs << features[i] << std::endl;
    }
  }

  if (show_weight == 1 || show_weight == 2){
    for (size_t i = 0; i < weights.size(); ++i){
      std::cout << weights[i] << std::endl;
    }
  } else if (show_weight == 2 || show_weight == 3){
    for (size_t i = 0; i < weights.size(); ++i){
      features_ofs << weights[i] << std::endl;
    }
  }

  features_ofs.close();
  return 0;
}
