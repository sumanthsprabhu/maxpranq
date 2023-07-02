#include "deep/NonlinCHCsolver.hpp"

using namespace ufo;
using namespace std;

static inline bool getBoolValue(const char * opt, bool defValue, int argc, char ** argv)
{
  for (int i = 1; i < argc; i++)
  {
    if (strcmp(argv[i], opt) == 0) return true;
  }
  return defValue;
}

int getIntValue(const char * opt, int defValue, int argc, char ** argv)
{
  for (int i = 1; i < argc-1; i++)
  {
    if (strcmp(argv[i], opt) == 0)
    {
      return atoi(argv[i+1]);
    }
  }
  return defValue;
}

int main (int argc, char ** argv)
{
  if (getBoolValue("--help", false, argc, argv) || argc == 1){
    outs () <<
        "* * *                              FreqHorn-Nonlin v.0.3 - Copyright (C) 2023                              * * *\n" <<
        "                                          Grigory Fedyukovich et al                                      \n\n" <<
        "Usage:                          Purpose:\n" <<
        " freqn [--help]                   show help\n" <<
        " freqn [options] <file.smt2>      discover invariants for a system of constrained Horn clauses\n\n" <<
        "Option:\n" <<
      " --max                            perform maximality check and refinement\n" <<
      " --dumpsmt                       Dump intermediate SMTs\n" <<
      " --ra                           Run maximality checking of Range Abduction\n" <<
      " --checknondet                  Check if CHC is non-deterministic\n\n";

    return 0;
  }
  int cex = getIntValue("--cex", 0, argc, argv);
  int str = getIntValue("--stren", 1, argc, argv);
  bool checkmax = getBoolValue("--max", false, argc, argv);
  bool checkra = getBoolValue("--ra", false, argc, argv);
  bool dumpsmt = getBoolValue("--dumpsmt", false, argc, argv);
  bool cndet = getBoolValue("--checknondet", false, argc, argv);
  solveNonlin(string(argv[argc-1]), cex, str, checkmax, checkra, dumpsmt, cndet);
  return 0;
}
