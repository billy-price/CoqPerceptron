#include <iostream>
#include <fstream>
#include <string>
using namespace std;

int main(int argc, char ** argv){
  ifstream times("times");
  ifstream fuels("fuels");

  ofstream vectors("vectors.plot");
  for (int i = 0; i < 5; ++i){
    int vec;
    string s;
    times >> s >> vec;
    vectors << vec << '\t';
    fuels >> s >> vec;
    int min, f;
    char c;
    double sec, timeCPP(0), timeOCAML(0), timeHS(0), fuel(0);
    for (int j = 0; j < 10; ++j){
      times >> min >> c >> sec >> c; timeCPP += 60*min + sec;
      times >> min >> c >> sec >> c; timeOCAML += 60*min + sec;
      times >> min >> c >> sec >> c; timeHS += 60*min + sec;
      fuels >> s >> f; fuel += f;
    }
    fuel /= 10.0; timeCPP /= 10.0; timeOCAML /= 10.0; timeHS /= 10.0;
    vectors << fuel << '\t'
            << timeCPP << '\t' << timeCPP/fuel << '\t' << timeCPP/vec << '\t'
            << timeOCAML << '\t' << timeOCAML/fuel << '\t' << timeOCAML/vec << '\t'
            << timeHS << '\t' << timeHS/fuel << '\t' << timeHS/vec << '\t' << endl;
  }

  for (int i = 0; i < 4; ++i){
    int vec;
    string s;
    times >> s >> vec;
    vectors << vec << '\t';
    fuels >> s >> vec;
    int min, f;
    char c;
    double sec, timeCPP(0), fuel(0);
    for (int j = 0; j < 10; ++j){
      times >> min >> c >> sec >> c; timeCPP += 60*min + sec;
      fuels >> s >> f; fuel += f;
    }
    fuel /= 10.0; timeCPP /= 10.0;
    vectors << fuel << '\t'
            << timeCPP << '\t' << timeCPP/fuel << '\t' << timeCPP/vec << '\t' << endl;
  } vectors.close();

  ofstream features("features.plot");
  for (int i = 0; i < 6; ++i){
    int feat;
    string s;
    times >> s >> feat;
    features << feat << '\t';
    fuels >> s >> feat;
    int min, f;
    char c;
    double sec, timeCPP(0), timeOCAML(0), timeHS(0), fuel(0);
    for (int j = 0; j < 10; ++j){
      times >> min >> c >> sec >> c; timeCPP += 60*min + sec;
      times >> min >> c >> sec >> c; timeOCAML += 60*min + sec;
      times >> min >> c >> sec >> c; timeHS += 60*min + sec;
      fuels >> s >> f; fuel += f;
    }
    fuel /= 10.0; timeCPP /= 10.0; timeOCAML /= 10.0; timeHS /= 10.0;
    features << fuel << '\t'
             << timeCPP << '\t' << timeCPP/fuel << '\t' << timeCPP/feat << '\t'
             << timeOCAML << '\t' << timeOCAML/fuel << '\t' << timeOCAML/feat << '\t'
             << timeHS << '\t' << timeHS/fuel << '\t' << timeHS/feat << endl;
  } features.close();

  ofstream Z("Z.plot");
  for (int i = 0; i < 8; ++i){
    int Zs;
    string s;
    times >> s >> Zs;
    Z << Zs << '\t';
    fuels >> s >> Zs;
    int min, f;
    char c;
    double sec, timeCPP(0), timeOCAML(0), timeHS(0), fuel(0);
    for (int j = 0; j < 10; ++j){
      times >> min >> c >> sec >> c; timeCPP += 60*min + sec;
      times >> min >> c >> sec >> c; timeOCAML += 60*min + sec;
      times >> min >> c >> sec >> c; timeHS += 60*min + sec;
      fuels >> s >> f; fuel += f;
    }
    fuel /= 10.0; timeCPP /= 10.0; timeOCAML /= 10.0; timeHS /= 10.0;
    Z << fuel << '\t'
      << timeCPP << '\t' << timeCPP/fuel << '\t' << timeCPP/Zs << '\t'
      << timeOCAML << '\t' << timeOCAML/fuel << '\t' << timeOCAML/Zs << '\t'
      << timeHS << '\t' << timeHS/fuel << '\t' << timeHS/Zs << endl;
  } Z.close();
  return 0;
}
