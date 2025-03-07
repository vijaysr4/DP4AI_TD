# TD 5 EUF Solver and Offline Lazy SMT-Solver

This repository contains an implementation of a theory solver for the theory of equality (EUF) and an offline lazy SMT-solver built on top of it. The EUF solver uses the congruence closure algorithm with union–find, and the lazy SMT-solver creates a Boolean abstraction of the input SMT-LIB formulas, enumerates Boolean models, and calls the EUF solver for theory reasoning.

## Repository Structure
~~~
.
├── euf.py                # Implementation of the EUF solver (congruence closure)
├── lazy_solver.py        # Offline lazy SMT-solver for the theory of equalities
├── test_lazy_solver.py   # Script to run the lazy SMT-solver on all test cases
├── test_solver.py        # Script to run tests on the EUF solver alone
├── utils.py              # Utility functions used by the EUF solver
└── test_cases/           # Folder containing SMT-LIB test cases (e.g., t0.smt2, t1.smt2, ...)
     ├── t0.smt2
     ├──  ....
     └── t9.smt2
~~~


## Prerequisites

- Python 3.x
- [PySMT](https://pysmt.readthedocs.io/en/latest/)
- An SMT solver backend (e.g., [Z3](https://github.com/Z3Prover/z3)) installed and available in your environment

You can install PySMT and Z3 with pip:

```bash
pip install pysmt
pysmt-install --z3
```

## Overview

### EUF Solver

The `euf.py` file implements a theory solver for the theory of equality. It:

- Extracts terms and splits equalities/inequalities from an input formula.
- Constructs an EGraph data structure using a union–find algorithm.
- Merges equalities and propagates congruence closure.
- Checks for consistency with respect to the provided inequalities.

Run the EUF solver tests using:

```bash
python test_solver.py
```
Output:
```bash
Runing test cases:
[SUCCESS] t0.smt2: returned Satisfiable
[SUCCESS] t1.smt2: returned Unsatisfiable
[SUCCESS] t2.smt2: returned Unsatisfiable
[SUCCESS] t3.smt2: returned Satisfiable
[SUCCESS] t4.smt2: returned Unsatisfiable
[SUCCESS] t5.smt2: returned Unsatisfiable
[SUCCESS] t6.smt2: returned Satisfiable
[SUCCESS] t7.smt2: returned Unsatisfiable
[SUCCESS] t8.smt2: returned Unsatisfiable
[SUCCESS] t9.smt2: returned Unsatisfiable
```

### Offline Lazy SMT-Solver

The `lazy_solver.py` file implements an offline lazy SMT-solver for the theory of equalities. It:

- Abstracts the theory atoms (equalities and their negations) in an SMT-LIB formula into Boolean variables.
- Enumerates Boolean models using a SAT solver.
- For each Boolean model, converts the assignment back to a theory candidate and checks it using the EUF solver.
- Blocks unsatisfiable Boolean assignments until a satisfiable model is found or the search is exhausted.

To run the lazy solver on a single test case:

```bash
python lazy_solver.py test_cases/t0.smt2
```

### Testing All Cases
The `test_lazy_solver.py` script iterates over all `.smt2` files in the test_cases folder and reports the satisfiability result for each case. Use:

```bash
python test_lazy_solver.py
```
Output:
```bash
t0.smt2: SATISFIABLE
t1.smt2: UNSATISFIABLE
t2.smt2: UNSATISFIABLE
t3.smt2: SATISFIABLE
t4.smt2: UNSATISFIABLE
t5.smt2: UNSATISFIABLE
t6.smt2: SATISFIABLE
t7.smt2: UNSATISFIABLE
t8.smt2: UNSATISFIABLE
t9.smt2: UNSATISFIABLE
```
