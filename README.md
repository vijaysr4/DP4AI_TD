# Decision Procedure for AI TD Projects Collection

This repository contains four independent SMT-based projects developed using PySMT and the Z3 SMT solver. Each project (TD 4–TD 7) demonstrates a different application of SMT techniques:

- **TD 4: Robot Path Planner**  
  Implements a robot path planner that computes bounded-length paths in a 2D environment with obstacles using SMT encodings.

- **TD 5: EUF Solver and Offline Lazy SMT-Solver**  
  Provides a theory solver for the theory of equality (EUF) using congruence closure and an offline lazy SMT-solver that abstracts SMT formulas into Boolean models.

- **TD 6: JSP Job Scheduling Solver**  
  Solves the Job Scheduling Problem using a disjunctive encoding to enforce job sequencing, machine disjunctivity, and to minimize the makespan.

- **TD 7: BMC & k-Induction Verification Tool**  
  Verifies safety properties of transition systems using Bounded Model Checking (BMC) and k-induction (with a simple path condition).

## Installation

### Dependencies

- **Python 3**  
- **PySMT**  
  Install with:
  ```bash
  pip install pysmt
  ```
- **Z3 SMT Solver**
  Install the Z3 backend for PySMT with:
  ```bash
  pysmt-install --z3
  ```
### Author: Vijay Venkatesh Murugan
### Program: M1 Data AI
### Institution: IP Paris
