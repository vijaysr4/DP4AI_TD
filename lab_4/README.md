# TD 4 Robot Path Planner using SMT and PySMT

This repository implements a robot path planner using SMT (Satisfiability Modulo Theories) and PySMT. The planner computes a bounded-length path for a robot moving in a 2D plane from a specified initial position to a target position while avoiding rectangular obstacles.

## File Structure 
```bash
.
├── README.md
├── one_step.smt2
├── multiple_step.smt2
├── single_plan.py
├── plan.py
└── maps
    ├── first.txt
    ├── obs_20_1.txt
    └── (other map files)
```
## Overview

The project contains both SMT-LIB encodings and Python-based planners:
- **one_step.smt2**: An SMT-LIB file encoding a single-step plan that moves the robot from the initial point to the target while avoiding obstacles.
- **multiple_step.smt2**: An SMT-LIB file encoding a bounded-length (multi-step) plan (e.g., with _k_ = 3 actions) that uses intermediate positions and directional constraints.
- **single_plan.py**: A Python script that generates and solves a single-step SMT encoding using PySMT and Z3.
- **plan.py**: A more advanced Python planner that constructs an SMT encoding for _k_ actions, solves it using Z3, and visualizes the resulting path using Tkinter.

## Requirements

- **Python 3**
- **PySMT**: Install via `pip install pysmt`
- **Z3 SMT Solver**: Install via `pysmt-install --z3`
- **Tkinter**: Usually included with Python (or install separately if needed)

## Map File Format

The map file is provided in JSON format and should include the following keys:
- **init**: The initial coordinates of the robot (e.g., `[[1, 1], [3, 1]]` to represent (1, 3) as a rational number).
- **target**: The target coordinates (e.g., `[[1, 1], [5, 1]]` for (1, 5)).
- **bounds**: A list of four rational numbers defining the map boundaries (e.g., `[[min_x, denom], [max_x, denom], [min_y, denom], [max_y, denom]]`).
- **obstacles**: A list of obstacles. Each obstacle is defined by four rational numbers representing its lower_x, upper_x, lower_y, and upper_y coordinates (e.g., `[[[3, 1], [5, 1], [2, 1], [4, 1]], ...]`).

## Usage

### SMT-LIB Files

To check the SMT encodings with Z3 directly:
```bash
z3 one_step.smt2
z3 multiple_step.smt2
```

## Python Planners
For the single-step planner:
```bash
python single_plan.py --map ./maps/first.txt
```
Output: 
```bash
Found path: [(Fraction(1, 1), Fraction(3, 1)), (Fraction(1, 1), Fraction(5, 1))]
```

For the bounded-length (multi-step) planner (e.g., with 3 actions):
```bash
python plan.py --map ./maps/obs_20_1.txt --k 3
```

