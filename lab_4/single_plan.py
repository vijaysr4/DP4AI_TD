"""
single_plan.py
--------------
A planner for a single action (one-step) robot path using PySMT.

This script reads a map from a JSON file, constructs an SMT encoding
that moves the robot from the initial point to the target point in one step,
solves the SMT problem using Z3, and prints the resulting path.
"""

import argparse
import json
from fractions import Fraction

from pysmt.typing import REAL, BOOL
from pysmt.shortcuts import Symbol, Real, And, Or, Not, Implies, Equals, GE, LE, Minus, Solver
from pysmt.logics import QF_LRA


# --- Map class to read the JSON map file ---
class Map:
    def __init__(self, map_file=None):
        # Default initialization; these will be PySMT Real objects.
        self.x0 = Real(0)
        self.y0 = Real(0)
        self.xf = Real(0)
        self.yf = Real(0)
        # We ignore obstacles for the single-plan version.
        if map_file is not None:
            self._read_map(map_file)

    def _read_map(self, map_file):
        with open(map_file, "r") as f:
            data = json.load(f)

            # Expecting the JSON file to contain "init" and "target" fields,
            # where each is a list of two numbers or a list of two lists.
            # Here, we assume each coordinate is given as a pair [numerator, denominator]
            # so that we can create a PySMT Real.
            def to_real(pair):
                # If the pair is like [1, 1] we create Real( Fraction(1,1) )
                from fractions import Fraction
                return Real(Fraction(pair[0], pair[1])) if isinstance(pair, list) else Real(pair)

            self.x0 = to_real(data["init"][0])
            self.y0 = to_real(data["init"][1])
            self.xf = to_real(data["target"][0])
            self.yf = to_real(data["target"][1])


# --- SMT Encoding for a single action ---
def get_encoding(map_):
    # Create SMT symbols.
    x0 = Symbol("x0", REAL)
    y0 = Symbol("y0", REAL)
    xf = Symbol("xf", REAL)
    yf = Symbol("yf", REAL)
    left = Symbol("left", BOOL)
    right = Symbol("right", BOOL)
    up = Symbol("up", BOOL)
    down = Symbol("down", BOOL)
    distance = Symbol("distance", REAL)

    # Constraint 1: Fix the initial and target positions.
    c_init_target = And(
        Equals(x0, map_.x0),
        Equals(y0, map_.y0),
        Equals(xf, map_.xf),
        Equals(yf, map_.yf)
    )

    # Constraint 2: One-hot encoding for the direction.
    c_one_hot = And(
        Or(left, right, up, down),
        And(
            Implies(left, And(Not(right), Not(up), Not(down))),
            Implies(right, And(Not(left), Not(up), Not(down))),
            Implies(up, And(Not(left), Not(right), Not(down))),
            Implies(down, And(Not(left), Not(right), Not(up)))
        )
    )

    # Constraint 3: Movement constraints.
    # If moving horizontally, then y0 must equal yf.
    c_hor = Implies(Or(left, right), Equals(y0, yf))
    # If moving vertically, then x0 must equal xf.
    c_ver = Implies(Or(up, down), Equals(x0, xf))

    # Constraint 4: Direction-specific ordering.
    c_order = And(
        Implies(left, GE(x0, xf)),
        Implies(right, LE(x0, xf)),
        Implies(up, LE(y0, yf)),
        Implies(down, GE(y0, yf))
    )

    # Constraint 5: Compute the distance moved.
    c_dist = And(
        Implies(Or(left, right), Equals(distance, Minus(xf, x0))),
        Implies(Or(up, down), Equals(distance, Minus(yf, y0)))
    )

    # Combine all constraints.
    encoding = And(c_init_target, c_one_hot, c_hor, c_ver, c_order, c_dist)
    return encoding


# --- Extract the model (trace) ---
def find_trace(encoding):
    # We extract the positions x0, y0, xf, yf from the model.
    x0 = Symbol("x0", REAL)
    y0 = Symbol("y0", REAL)
    xf = Symbol("xf", REAL)
    yf = Symbol("yf", REAL)

    def get_fraction(val):
        return Fraction(val.serialize())

    trace = []
    with Solver(name="z3", logic=QF_LRA) as solver:
        solver.add_assertion(encoding)
        if solver.check_sat():
            trace = [
                (get_fraction(solver.get_value(x0)), get_fraction(solver.get_value(y0))),
                (get_fraction(solver.get_value(xf)), get_fraction(solver.get_value(yf)))
            ]
    return trace


# --- Main function ---
def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--map", required=True, help="Path to map JSON file")
    args = parser.parse_args()

    map_ = Map(args.map)
    encoding = get_encoding(map_)
    trace = find_trace(encoding)

    if trace:
        print("Found path:", trace)
    else:
        print("No path found.")


if __name__ == '__main__':
    main()
