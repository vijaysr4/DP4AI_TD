#!/usr/bin/env python3
# jsp.py
# Encode the job scheduling problem

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
    is_valid,
    Solver,
    Symbol, TRUE, FALSE, get_env,
    Real, Int,
    Not, And, Or, Implies, Iff, Equals,
    GE, GT, LT, LE, Max,
    ExactlyOne
)
from pysmt.logics import QF_LIA

class JSP:
    def __init__(self,
                 tot_machines = None,
                 jobs = None):
        # You can pass custom parameters, but here we hard-code an example.
        self.tot_machines = 3
        self.jobs = [ [(0,3), (1,2), (2,2)],
                      [(0,2), (2,1), (1,3)],
                      [(1,4), (2,3)]]

        self.tasks_for_machine = { }
        for i in range(self.tot_machines):
            self.tasks_for_machine[i] = []
        i = 0
        for tasks in self.jobs:
            j = 0
            for t in tasks:
                self.tasks_for_machine[t[0]].append((i,j))
                j += 1
            i += 1

    def duration(self, i, j):
        # i is the index of the job, j is the index of the task in that job.
        return self.jobs[i][j][1]

    def machine(self, i, j):
        return self.jobs[i][j][0]

    def get_max_duration(self):
        # A rough upper bound: sum of durations for all tasks.
        max_duration = 0
        for i in range(len(self.jobs)):
            for j in range(len(self.jobs[i])):
                max_duration += self.duration(i,j)
        return max_duration

def get_disjunctive_encoding(problem):
    # 0. Variables: start time of task i,j.
    varlist = {}
    for i in range(len(problem.jobs)):
        job_tasks = {}
        for j in range(len(problem.jobs[i])):
            m = problem.machine(i,j)
            var = Symbol('t_%d_%d_m%d' % (i, j, m), INT)
            job_tasks[j] = var
        varlist[i] = job_tasks

    # 1. Non-negative constraints: All task start times are >= 0.
    non_negative = And([varlist[i][j] >= 0
                        for i in range(len(problem.jobs))
                        for j in range(len(problem.jobs[i]))])

    # 2. Job sequencing: tasks in each job occur sequentially.
    sequence = And([varlist[i][j+1] >= varlist[i][j] + problem.duration(i,j)
                    for i in range(len(problem.jobs))
                    for j in range(len(problem.jobs[i]) - 1)])

    # 3. Machine constraints: tasks on the same machine do not overlap.
    machine_constraints = []
    for m in range(problem.tot_machines):
        tasks = problem.tasks_for_machine[m]
        for idx1 in range(len(tasks)):
            for idx2 in range(idx1+1, len(tasks)):
                i, j = tasks[idx1]
                i2, j2 = tasks[idx2]
                t1 = varlist[i][j]
                t2 = varlist[i2][j2]
                d1 = problem.duration(i,j)
                d2 = problem.duration(i2,j2)
                # Either the first task finishes before the second starts,
                # or the second finishes before the first starts.
                machine_constraints.append(Or(t1 + d1 <= t2, t2 + d2 <= t1))
    machine_constraint = And(machine_constraints)

    # 4. Makespan constraint: tmax is greater than or equal to every task's finish time.
    tmax = Symbol("tmax", INT)
    max_time_constraints = []
    for i in range(len(problem.jobs)):
        for j in range(len(problem.jobs[i])):
            max_time_constraints.append(tmax >= varlist[i][j] + problem.duration(i,j))
    max_time = And(max_time_constraints)

    encoding = And(non_negative, sequence, machine_constraint, max_time)
    return encoding, varlist, tmax

def optimize(problem, encoding, tmax):
    """
    Uses binary search to find the minimal feasible makespan.
    Returns the model with optimal makespan and its value.
    """
    ub = problem.get_max_duration()  # Upper bound for tmax.
    lb = 0                         # Lower bound.
    best_model = None
    best_value = None

    # Binary search on the makespan.
    while lb <= ub:
        mid = (lb + ub) // 2
        # Add constraint: tmax <= mid.
        current_constraint = And(encoding, tmax <= Int(mid))
        with Solver(name="z3", logic=QF_LIA) as solver:
            solver.add_assertion(current_constraint)
            if solver.solve():
                best_model = solver.get_model()
                best_value = mid
                # Try for a smaller makespan.
                ub = mid - 1
            else:
                lb = mid + 1
    return best_model, best_value

def main():
    problem = JSP()
    encoding, varlist, tmax = get_disjunctive_encoding(problem)

    # Check for feasibility of the basic encoding.
    with Solver(name="z3", logic=QF_LIA) as solver:
        solver.add_assertion(encoding)
        if solver.solve():
            print("The encoding is feasible")
        else:
            print("The encoding is not feasible")
            return

    # Optimization: find the schedule with minimal makespan.
    model, optimal_makespan = optimize(problem, encoding, tmax)
    if model is not None:
        print("Optimal makespan found:", optimal_makespan)
        # Print the schedule for each task.
        for i in range(len(problem.jobs)):
            for j in range(len(problem.jobs[i])):
                task_start = model.get_value(varlist[i][j])
                m = problem.machine(i,j)
                d = problem.duration(i,j)
                print("Job %d, Task %d on machine %d: start at %s, duration %d" %
                      (i, j, m, task_start, d))
    else:
        print("No optimal schedule found.")

if __name__ == '__main__':
    main()
