MaxPrANQ
========

Weakest precondition inference for non-deterministic programs represents as CHCs. 

Installation
============

Compiles with gcc-5 (on Linux) and clang-900 (on Mac).  

* `cd maxpranq ; mkdir build ; cd build`
* `cmake ../`
* `make` to build dependencies (Z3)
* `make` (again) to build MaxPrANQ

After compilation, the binary of MaxPrANQ  will be at `build/tools/nonlin/`. Run with `--max` option to generate weakest precondition.

Benchmarks
==========

Collection of the SMT-LIB2 translations of the precondition inference tasks can be found at `bench_precondn/fmcad_bench`. MaxPrANQ is expected to first find a valid precondition (this is the interpretation it generates first time when it outputs `unsat`) and then check maximality and weaken. If it has decided a precondition is the weakest then it gives the message `maximal!`. If it has generated a valid invariant but was unable to decide its maximality then it gives the message `may not be maximal`.

Running Evaluation of TACAS'24
==============================

You may run MaxPrANQ on all the benchmarks from `bench_precondn/tacas24_bench` by running the script `bash runall.sh`. It should complete within a few minutes. After completion, a summary of results along with the path of the log directory is displayed. The generated preconditions for each benchmark will be in `output/tty_benchmark` in the log directory.

