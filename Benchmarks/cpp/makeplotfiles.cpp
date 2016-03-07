#include <iostream>
#include <fstream>
#include <string>
using namespace std;

int main(int argc, char ** argv){
  ifstream fuels("output/fuels");
  ifstream cpptimes("output/cpptimes");
  ifstream hstimes("output/hstimes");
  ifstream hsopttimes("output/hsopttimes");

  ofstream vectors("plots/vectors.plot");
  for (int i = 0; i < 6; ++i){
    int vec;
    string s;
    cpptimes >> s >> vec;
    hstimes >> s >> vec;
    hsopttimes >> s >> vec;
    vectors << vec << '\t';
    fuels >> s >> vec;
    int min, f;
    char c;
    double sec, timeCPP(0), timeHS(0), timeHSOpt(0), fuel(0);
    for (int j = 0; j < 10; ++j){
      cpptimes >> min >> c >> sec >> c; timeCPP += 60*min + sec;
      hstimes >> min >> c >> sec >> c; timeHS += 60*min + sec;
      hsopttimes >> min >> c >> sec >> c; timeHSOpt += 60*min + sec;
      fuels >> s >> f; fuel += f;
    }
    fuel /= 10.0; timeCPP /= 10.0; timeHS /= 10.0; timeHSOpt /= 10.0;
    vectors << fuel << '\t'
            << timeCPP << '\t' << timeCPP/fuel << '\t' << timeCPP/vec << '\t'
            << timeHSOpt << '\t' << timeHSOpt/fuel << '\t' << timeHSOpt/vec << '\t'
            << timeHS << '\t' << timeHS/fuel << '\t' << timeHS/vec << endl;
  }

  for (int i = 0; i < 3; ++i){
    int vec;
    string s;
    cpptimes >> s >> vec;
    hsopttimes >> s >> vec;
    vectors << vec << '\t';
    fuels >> s >> vec;
    int min, f;
    char c;
    double sec, timeCPP(0), timeHSOpt(0), fuel(0);
    for (int j = 0; j < 10; ++j){
      cpptimes >> min >> c >> sec >> c; timeCPP += 60*min + sec;
      hsopttimes >> min >> c >> sec >> c; timeHSOpt += 60*min + sec;
      fuels >> s >> f; fuel += f;
    }
    fuel /= 10.0; timeCPP /= 10.0; timeHSOpt /= 10.0;
    vectors << fuel << '\t'
            << timeCPP << '\t' << timeCPP/fuel << '\t' << timeCPP/vec << '\t'
            << timeHSOpt << '\t' << timeHSOpt/fuel << '\t' << timeHSOpt/vec << endl;
  } vectors.close();

  ofstream features("plots/features.plot");
  for (int i = 0; i < 6; ++i){
    int feat;
    string s;
    cpptimes >> s >> feat;
    hstimes >> s >> feat;
    hsopttimes >> s >> feat;
    features << feat << '\t';
    fuels >> s >> feat;
    int min, f;
    char c;
    double sec, timeCPP(0), timeHS(0), timeHSOpt(0), fuel(0);
    for (int j = 0; j < 10; ++j){
      cpptimes >> min >> c >> sec >> c; timeCPP += 60*min + sec;
      hstimes >> min >> c >> sec >> c; timeHS += 60*min + sec;
      hsopttimes >> min >> c >> sec >> c; timeHSOpt += 60*min + sec;
      fuels >> s >> f; fuel += f;
    }
    fuel /= 10.0; timeCPP /= 10.0; timeHS /= 10.0; timeHSOpt /= 10.0;
    features << fuel << '\t'
             << timeCPP << '\t' << timeCPP/fuel << '\t' << timeCPP/feat << '\t'
             << timeHSOpt << '\t' << timeHSOpt/fuel << '\t' << timeHSOpt/feat << '\t'
             << timeHS << '\t' << timeHS/fuel << '\t' << timeHS/feat << endl;
  } features.close();

  ofstream Z("plots/Z.plot");
  for (int i = 0; i < 8; ++i){
    int Zs;
    string s;
    cpptimes >> s >> Zs;
    hstimes >> s >> Zs;
    hsopttimes >> s >> Zs;
    Z << Zs << '\t';
    fuels >> s >> Zs;
    int min, f;
    char c;
    double sec, timeCPP(0), timeHS(0), timeHSOpt(0), fuel(0);
    for (int j = 0; j < 10; ++j){
      cpptimes >> min >> c >> sec >> c; timeCPP += 60*min + sec;
      hstimes >> min >> c >> sec >> c; timeHS += 60*min + sec;
      hsopttimes >> min >> c >> sec >> c; timeHSOpt += 60*min + sec;
      fuels >> s >> f; fuel += f;
    }
    fuel /= 10.0; timeCPP /= 10.0; timeHS /= 10.0; timeHSOpt /= 10.0;
    Z << fuel << '\t'
      << timeCPP << '\t' << timeCPP/fuel << '\t' << timeCPP/Zs << '\t'
      << timeHSOpt << '\t' << timeHSOpt/fuel << '\t' << timeHSOpt/Zs << '\t'
      << timeHS << '\t' << timeHS/fuel << '\t' << timeHS/Zs << endl;
  } Z.close();
  return 0;
}
