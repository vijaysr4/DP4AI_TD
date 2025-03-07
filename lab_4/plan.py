""" Find a path for the robot
"""

from math import floor, ceil
import argparse
from tkinter import Tk, Canvas, LAST
import os
import sys
import json
from fractions import Fraction
import functools

from pysmt.typing import BOOL, REAL, INT
from pysmt.shortcuts import (
    Solver, Symbol, Real, Int,
    And, Or, Not, Implies, Iff, Equals,
    GE, GT, LT, LE, Minus
)
from pysmt.logics import QF_LRA

# --- Map class to read the map file (JSON) ---
class Map():
    def __init__(self, map_file=None):
        # Bounds of the map (as PySMT Real objects)
        self.min_x = Real(0)
        self.min_y = Real(0)
        self.max_x = Real(0)
        self.max_y = Real(0)
        # Coordinates of the initial point
        self.x0 = Real(0)
        self.y0 = Real(0)
        # Coordinates of the target point
        self.xf = Real(0)
        self.yf = Real(0)
        # List of obstacles, each as a tuple: (lower_x, upper_x, lower_y, upper_y)
        self.obstacles = []
        if map_file is not None:
            self._read_map(map_file)

    def _read_map(self, input_map):
        def read_rational(json_data):
            assert len(json_data) == 2
            from fractions import Fraction
            return Real(Fraction(json_data[0], json_data[1]))
        with open(input_map) as f:
            data = json.load(f)
            # Check for required keys
            for key in ["init", "target", "obstacles", "bounds"]:
                assert key in data
            assert len(data["bounds"]) == 4
            self.min_x = read_rational(data["bounds"][0])
            self.max_x = read_rational(data["bounds"][1])
            self.min_y = read_rational(data["bounds"][2])
            self.max_y = read_rational(data["bounds"][3])
            assert len(data["init"]) == 2
            self.x0 = read_rational(data["init"][0])
            self.y0 = read_rational(data["init"][1])
            assert len(data["target"]) == 2
            self.xf = read_rational(data["target"][0])
            self.yf = read_rational(data["target"][1])
            for obs in data["obstacles"]:
                assert len(obs) == 4
                self.obstacles.append((
                    read_rational(obs[0]),
                    read_rational(obs[1]),
                    read_rational(obs[2]),
                    read_rational(obs[3])
                ))

# --- Visualization using Tkinter ---
def draw(map_1, trace):
    top = Tk()
    has_trace = len(trace) > 0
    if not has_trace:
        trace = [
            (Fraction(map_1.x0.serialize()), Fraction(map_1.y0.serialize())),
            (Fraction(map_1.xf.serialize()), Fraction(map_1.yf.serialize()))
        ]
    def to_float(f):
        return 0 if f.denominator == 0 else float(f.numerator) / float(f.denominator)
    canvas_width = 500
    canvas_height = 500
    min_x = functools.reduce(lambda res, elem: res if res <= to_float(elem[0]) else to_float(elem[0]), trace, -6)
    max_x = functools.reduce(lambda res, elem: res if res >= to_float(elem[0]) else to_float(elem[0]), trace, 6)
    min_y = functools.reduce(lambda res, elem: res if res <= to_float(elem[1]) else to_float(elem[1]), trace, -6)
    max_y = functools.reduce(lambda res, elem: res if res >= to_float(elem[1]) else to_float(elem[1]), trace, 6)
    def point_in_canvas(x,y):
        def point_in_canvas_aux(x, min_x, max_x, width):
            return ((x - min_x) / (max_x - min_x)) * width
        bound = 10
        w_visible = canvas_width - 2*bound
        h_visible = canvas_height - 2*bound
        return (float(bound + point_in_canvas_aux(x, min_x, max_x, w_visible)),
                float(bound + h_visible - point_in_canvas_aux(y, min_y, max_y, h_visible)))
    w = Canvas(top, width=canvas_width, height=canvas_height)
    (min_x_canvas, min_y_canvas) = point_in_canvas(min_x, min_y)
    (max_x_canvas, max_y_canvas) = point_in_canvas(max_x, max_y)
    (origin_x, origin_y) = point_in_canvas(0,0)
    w.create_line(min_x_canvas, origin_y, max_x_canvas, origin_y, dash=(4,2))
    w.create_line(origin_x, min_y_canvas, origin_x, max_y_canvas, dash=(4,2))
    for x in range(floor(min_x), ceil(max_x)):
        (x_canvas, _) = point_in_canvas(x, 0)
        w.create_text(x_canvas, origin_y+10, fill="black", text=str(x))
    for y in range(floor(min_y), ceil(max_y)):
        (_, y_canvas) = point_in_canvas(0, y)
        w.create_text(origin_x-10, y_canvas, fill="black", text=str(y))
    # Draw obstacles
    for obs in map_1.obstacles:
        x_lower, x_upper, y_lower, y_upper = obs
        (x_low_c, y_low_c) = point_in_canvas(to_float(Fraction(str(x_lower))),
                                             to_float(Fraction(str(y_lower))))
        (x_high_c, y_high_c) = point_in_canvas(to_float(Fraction(str(x_upper))),
                                               to_float(Fraction(str(y_upper))))
        w.create_rectangle(x_low_c, y_high_c, x_high_c, y_low_c,
                           outline='red', fill='blue')
    # Draw trace
    px, py = None, None
    for (x, y) in trace:
        (x_canvas, y_canvas) = point_in_canvas(to_float(x), to_float(y))
        radius = 5
        w.create_oval(x_canvas - radius, y_canvas + radius,
                      x_canvas + radius, y_canvas - radius,
                      fill='red')
        if has_trace and px is not None:
            w.create_line(px, py, x_canvas, y_canvas, arrow=LAST)
        px, py = x_canvas, y_canvas
    w.pack()
    top.mainloop()

# --- SMT Encoding for k-step Path (Exercise 4) ---
def avoid_obstacle(xs, ys, xd, yd, x_low, x_high, y_low, y_high):
    """
    Returns a PySMT formula ensuring that the segment from (xs,ys) to (xd,yd)
    avoids the rectangular obstacle defined by [x_low, x_high] x [y_low, y_high].
    The segment avoids the obstacle if both endpoints lie entirely on one side
    (left, right, below, or above) of the obstacle.
    """
    return Or(
        And(LE(xs, x_low), LE(xd, x_low)),      # entirely to the left
        And(GE(xs, x_high), GE(xd, x_high)),      # entirely to the right
        And(LE(ys, y_low), LE(yd, y_low)),         # entirely below
        And(GE(ys, y_high), GE(yd, y_high))         # entirely above
    )

def get_encoding(map_1, k):
    """
    Returns the PySMT encoding for a robot path with k actions.
    Creates k+1 position variables (x_i, y_i for i=0...k), fixes the initial and target,
    and for each action i (0 to k-1) adds:
      - Four Boolean direction variables (left_i, right_i, up_i, down_i) with one-hot constraint.
      - Movement constraints: horizontal moves keep y constant; vertical moves keep x constant.
      - Direction-specific ordering constraints.
      - Obstacle avoidance constraints for each segment.
    """
    from pysmt.shortcuts import Symbol, Real, And, Or, Not, Implies, Equals, GE, LE
    from pysmt.typing import REAL, BOOL

    constraints = []

    # Create position variables for steps 0 ... k.
    xs = [Symbol("x_%d" % i, REAL) for i in range(k+1)]
    ys = [Symbol("y_%d" % i, REAL) for i in range(k+1)]

    # Fix initial and target positions.
    constraints.append(Equals(xs[0], map_1.x0))
    constraints.append(Equals(ys[0], map_1.y0))
    constraints.append(Equals(xs[k], map_1.xf))
    constraints.append(Equals(ys[k], map_1.yf))

    # For each action step, add direction and movement constraints.
    for i in range(k):
        # Create Boolean variables for directions.
        left = Symbol("left_%d" % i, BOOL)
        right = Symbol("right_%d" % i, BOOL)
        up = Symbol("up_%d" % i, BOOL)
        down = Symbol("down_%d" % i, BOOL)

        # One-hot: exactly one direction is true.
        one_hot = And(
            Or(left, right, up, down),
            And(
                Implies(left, And(Not(right), Not(up), Not(down))),
                Implies(right, And(Not(left), Not(up), Not(down))),
                Implies(up, And(Not(left), Not(right), Not(down))),
                Implies(down, And(Not(left), Not(right), Not(up)))
            )
        )
        constraints.append(one_hot)

        # Movement constraints:
        # If moving horizontally, y remains constant.
        constraints.append(Implies(Or(left, right), Equals(ys[i], ys[i+1])))
        # If moving vertically, x remains constant.
        constraints.append(Implies(Or(up, down), Equals(xs[i], xs[i+1])))
        # Direction ordering:
        constraints.append(Implies(left, GE(xs[i], xs[i+1])))
        constraints.append(Implies(right, LE(xs[i], xs[i+1])))
        constraints.append(Implies(up, LE(ys[i], ys[i+1])))
        constraints.append(Implies(down, GE(ys[i], ys[i+1])))

        # Obstacle avoidance for each segment: for every obstacle in map_1.obstacles.
        for obs in map_1.obstacles:
            x_low, x_high, y_low, y_high = obs
            constraints.append(avoid_obstacle(xs[i], ys[i], xs[i+1], ys[i+1],
                                              x_low, x_high, y_low, y_high))
    from pysmt.shortcuts import And
    return And(constraints)

def find_trace(encoding, k):
    """
    Solves the SMT encoding and returns a list of (x,y) points (as Fraction objects)
    representing the robot's path (positions at steps 0...k).
    """
    from pysmt.shortcuts import Solver, Symbol, Real
    from fractions import Fraction
    # Recreate the position symbols.
    xs = [Symbol("x_%d" % i, REAL) for i in range(k+1)]
    ys = [Symbol("y_%d" % i, REAL) for i in range(k+1)]
    def get_fraction(val):
        return Fraction(val.serialize())
    trace = []
    with Solver(name="z3", logic=QF_LRA) as solver:
        solver.add_assertion(encoding)
        if solver.check_sat():
            for i in range(k+1):
                x_val = solver.get_value(xs[i])
                y_val = solver.get_value(ys[i])
                trace.append((get_fraction(x_val), get_fraction(y_val)))
    return trace

# --- Main function ---
def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--map", required=True, help="Path to the map file (JSON)")
    parser.add_argument("--k", default=1, type=int, help="Number of actions")
    args = parser.parse_args()

    map_file = args.map
    map_1 = Map(map_file)

    k = args.k
    encoding = get_encoding(map_1, k)
    trace = find_trace(encoding, k)

    if trace:
        draw(map_1, trace)
    else:
        print("Did not find a path of %d steps" % k)
        draw(map_1, [])

if __name__ == '__main__':
    main()
