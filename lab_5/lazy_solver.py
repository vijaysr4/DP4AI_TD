"""
Offline Lazy SMT-solver for the theory of equalities.
Uses the euf_solver from euf.py as the theory solver.
"""

from pysmt.shortcuts import (
    Symbol, And, Or, Not, Implies, Iff, Solver, get_model, is_sat, simplify
)
from pysmt.typing import BOOL
from pysmt.logics import QF_UF
from euf import euf_solver

def boolean_abstraction(formula, mapping):
    """
    Recursively build a Boolean abstraction of the input formula.
    Every theory atom (i.e. an equality or its negation) is replaced by
    a fresh Boolean variable and stored in mapping.

    mapping: a dictionary that will associate each theory atom (a PySMT formula)
    to its corresponding Boolean variable.
    """
    # If the formula is already a symbol or a Boolean constant, return it.
    if formula.is_symbol() or formula.is_bool_constant():
        return formula
    # If the formula is an equality or the negation of an equality,
    # treat it as a theory atom.
    if formula.is_equals() or (formula.is_not() and formula.arg(0).is_equals()):
        # Use the formula itself as key
        if formula not in mapping:
            b = Symbol("b_%d" % len(mapping), BOOL)
            mapping[formula] = b
        return mapping[formula]
    # Recurse on common Boolean connectives.
    if formula.is_not():
        return Not(boolean_abstraction(formula.arg(0), mapping))
    if formula.is_and():
        return And([boolean_abstraction(arg, mapping) for arg in formula.args()])
    if formula.is_or():
        return Or([boolean_abstraction(arg, mapping) for arg in formula.args()])
    if formula.is_implies():
        return Or(Not(boolean_abstraction(formula.arg(0), mapping)),
                  boolean_abstraction(formula.arg(1), mapping))
    if formula.is_iff():
        left = boolean_abstraction(formula.arg(0), mapping)
        right = boolean_abstraction(formula.arg(1), mapping)
        return And(Implies(left, right), Implies(right, left))
    # Fall-back: return the formula itself (this should not occur in our setting)
    return formula

def offline_lazy_smt_solver(formula):
    """
    Offline lazy SMT-solver for the theory of equalities.

    1. Build the Boolean abstraction of the input formula.
    2. Enumerate Boolean models.
    3. For each Boolean model, construct the corresponding theory assignment
       (conjunction of theory atoms and their negations) and check it with euf_solver.
    4. If the theory check fails, block that Boolean model and continue.

    Returns True if the formula is satisfiable, False otherwise.
    """
    # Build the Boolean abstraction.
    mapping = {}  # maps theory atoms (and their negations) to Boolean symbols.
    bool_abstr = boolean_abstraction(formula, mapping)

    # We'll refine the Boolean formula by adding blocking clauses.
    refined_bool = bool_abstr
    sat_solver = Solver(name="z3", logic=QF_UF)

    while sat_solver.solve(assumptions=[refined_bool]):
        model = sat_solver.get_model()
        # Construct the theory candidate:
        # For each theory atom (the key in mapping), if its associated Boolean variable is True in the model,
        # include the atom; otherwise include its negation.
        theory_literals = []
        for atom, b in mapping.items():
            if model.get_value(b).is_true():
                theory_literals.append(atom)
            else:
                theory_literals.append(Not(atom))
        theory_candidate = And(theory_literals)

        # Check the theory candidate using the euf_solver.
        if euf_solver(theory_candidate):
            # Found a Boolean model that is theory-satisfiable.
            return True
        else:
            # Build a blocking clause: it forces at least one Boolean variable to take a different value.
            block_clause = Or([Not(b) if model.get_value(b).is_true() else b for atom, b in mapping.items()])
            refined_bool = And(refined_bool, block_clause)

    # No Boolean model yielded a theory-satisfiable assignment.
    return False


def main():
    """
    Minimal demo: read an SMT-LIB formula from a file, run the offline lazy SMT-solver,
    and print the result.
    """
    import sys
    if len(sys.argv) < 2:
        print("Usage: python lazy_solver.py <input_file.smt2>")
        sys.exit(1)

    filename = sys.argv[1]
    from pysmt.smtlib.parser import SmtLibParser
    parser = SmtLibParser()
    with open(filename) as f:
        script = parser.get_script(f)
        formula = script.get_last_formula()

    result = offline_lazy_smt_solver(formula)
    if result:
        print("SATISFIABLE")
    else:
        print("UNSATISFIABLE")

if __name__ == '__main__':
    main()
