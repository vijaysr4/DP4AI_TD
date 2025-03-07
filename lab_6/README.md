# TD 6 JSP Job Scheduling Solver

This repository contains a Python-based solver for the Job Scheduling Problem (JSP) using a disjunctive encoding with the [PySMT](https://pysmt.readthedocs.io/en/latest/) library and the Z3 SMT solver.

## Overview

The Job Scheduling Problem (JSP) involves scheduling a set of jobs, where each job is composed of a sequence of tasks. Each task requires a specific machine for a given duration. The solver encodes the following constraints:

- **Non-Negativity:** Every task's start time must be greater than or equal to 0.
- **Job Sequencing:** Tasks within each job must be executed in order, meaning each subsequent task starts after the previous one finishes.
- **Machine Disjunctivity:** Tasks running on the same machine must not overlap.
- **Makespan Optimization:** The objective is to minimize the makespan (i.e., the maximum completion time of all tasks).

## Files

- `jsp.py`: Contains the full implementation:
  - A `JSP` class that defines a sample problem instance.
  - Functions to encode the problem constraints using PySMT.
  - An optimization routine that uses binary search on the makespan to find the optimal schedule.
  - Code to output the schedule if a feasible and optimal solution is found.

## Usage
Run the solver using: 
```bash
python jsp.py
```

Output
```bash
The encoding is feasible
Optimal makespan found: 10
Job 0, Task 0 on machine 0: start at 2, duration 3
Job 0, Task 1 on machine 1: start at 5, duration 2
Job 0, Task 2 on machine 2: start at 8, duration 2
Job 1, Task 0 on machine 0: start at 0, duration 2
Job 1, Task 1 on machine 2: start at 4, duration 1
Job 1, Task 2 on machine 1: start at 7, duration 3
Job 2, Task 0 on machine 1: start at 1, duration 4
Job 2, Task 1 on machine 2: start at 5, duration 3
```

Let's verify the constraints step by step:

### Job Sequencing
- **Job 0:**
  - **Task 0:** Machine 0, start = 2, duration = 3 → finish at 5.
  - **Task 1:** Machine 1, start = 5, duration = 2 → finish at 7.
  - **Task 2:** Machine 2, start = 8, duration = 2 → finish at 10.  
  The tasks are in order since 5 ≤ 5, and 7 ≤ 8.

- **Job 1:**
  - **Task 0:** Machine 0, start = 0, duration = 2 → finish at 2.
  - **Task 1:** Machine 2, start = 4, duration = 1 → finish at 5.
  - **Task 2:** Machine 1, start = 7, duration = 3 → finish at 10.  
  Here, 2 ≤ 4 and 5 ≤ 7, so ordering is respected.

- **Job 2:**
  - **Task 0:** Machine 1, start = 1, duration = 4 → finish at 5.
  - **Task 1:** Machine 2, start = 5, duration = 3 → finish at 8.  
  The second task starts right when the first finishes.

### Machine Constraints (No Overlap)
- **Machine 0:**  
  - Job 1, Task 0 (0 to 2) and Job 0, Task 0 (2 to 5) do not overlap.
  
- **Machine 1:**  
  - Job 2, Task 0 (1 to 5), Job 0, Task 1 (5 to 7), and Job 1, Task 2 (7 to 10) are scheduled back-to-back.
  
- **Machine 2:**  
  - Job 1, Task 1 (4 to 5), Job 2, Task 1 (5 to 8), and Job 0, Task 2 (8 to 10) follow sequentially.

### Makespan Verification
- The makespan is reported as **10**.  
- The latest finish times are Job 0, Task 2 and Job 1, Task 2, both finishing at 10, which matches the reported makespan.

### Conclusion
All constraints—non-negativity, job sequencing, and machine disjunctivity—are satisfied, and the optimal makespan is correctly determined as 10.

