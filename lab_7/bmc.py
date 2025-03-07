import argparse
import sys
from io import StringIO

from pysmt.typing import BOOL, INT
from pysmt.shortcuts import Symbol, TRUE, FALSE, Not, And, Or, Equals, get_env, substitute, Solver
from pysmt.exceptions import SolverAPINotFound
from pysmt.smtlib.parser import SmtLibParser

from ts import TS


def parse_formula(formula_str):
    """
    Parse a formula string into a pysmt formula using SmtLibParser.
    (This helper expects the string to represent a single formula—not a full SMT-LIB script.)
    """
    env = get_env()
    parser = SmtLibParser(env)
    return parser.get_formula(StringIO(formula_str))


def convert_type(typename):
    """
    Convert a type given as a string (e.g., "Bool", "Int") to the corresponding pysmt type.
    If typename is already a pysmt type, return it.
    """
    if isinstance(typename, str):
        t = typename.lower()
        if t in ("bool", "boolean"):
            return BOOL
        elif t in ("int", "integer"):
            return INT
        else:
            # Default to BOOL if unknown; adjust as needed.
            return BOOL
    return typename


def get_symbol_from_var(ts, var):
    """
    Given an element from ts.state_vars, if it is already a pysmt Symbol, return it.
    Otherwise, assume var is a string and return a new Symbol of type BOOL.
    (You can adjust the default type if needed.)
    """
    if hasattr(var, "symbol_name"):
        return var
    return Symbol(var, BOOL)


def rename_f(ts, formula, i):
    """
    Given a formula containing ts.state_vars, replace each state variable v with v_bmc_i
    and each next variable for v with v_bmc_(i+1).
    """
    replace_map = {}
    for var in ts.state_vars:
        sym = get_symbol_from_var(ts, var)
        t = convert_type(sym.symbol_type())
        new_sym = Symbol("%s_bmc_%d" % (sym.symbol_name(), i), t)
        replace_map[sym] = new_sym
        v_next = ts.next_f(sym)
        new_v_next = Symbol("%s_bmc_%d" % (sym.symbol_name(), i + 1), t)
        replace_map[v_next] = new_v_next
    renamed = substitute(formula, replace_map)
    return renamed


def fromStringFormula(ts, string):
    """
    Parse a string as an SMT formula by declaring all state variables first.
    (Used for demonstration only.)
    """

    def fromString(parser, string):
        output = StringIO()
        output.write(string)
        output.seek(0)
        try:
            script = parser.get_script(output)
        except Exception as e:
            output.seek(0)
            print("Error parsing the SMT expression:")
            print(output.getvalue())
            raise e
        return script

    parser = SmtLibParser(ts.env)
    smt_script = ""
    for v in ts.state_vars:
        sym = get_symbol_from_var(ts, v)
        t = convert_type(sym.symbol_type())
        smt_script += "(declare-fun %s () %s)\n" % (sym.symbol_name(), str(t))
    smt_script += "(assert %s)" % string
    script = fromString(parser, smt_script)
    return script.get_last_formula()


def simple_path_formula(ts, k):
    """
    Build the simple path condition:
      For every pair of time indices 0 <= i < j <= k,
      there exists at least one state variable v in ts.state_vars such that:
          v^i != v^j.
    """
    constraints = []
    for i in range(0, k + 1):
        for j in range(i + 1, k + 1):
            diff_conds = []
            for v in ts.state_vars:
                sym = get_symbol_from_var(ts, v)
                v_i = rename_f(ts, sym, i)
                v_j = rename_f(ts, sym, j)
                diff_conds.append(Not(Equals(v_i, v_j)))
            constraints.append(Or(diff_conds))
    return And(constraints) if constraints else TRUE()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--input")
    parser.add_argument("--k", default=0, type=int, help="Bound for BMC or induction (k-induction)")
    parser.add_argument("--i", default=False, type=bool, help="If True, perform induction instead of plain BMC")
    args = parser.parse_args()

    input_file = args.input
    k = args.k
    use_induction = args.i

    env = get_env()
    with open(input_file, "r") as f:
        print("Reading %s" % input_file)
        (ts, prop) = TS.from_vmt(f, env)

    # Force ts.state_vars to be proper pysmt Symbols.
    ts.state_vars = {get_symbol_from_var(ts, v) for v in ts.state_vars}

    # Check that ts.init, ts.trans, and prop are parsed formulas.
    if not hasattr(ts.init, "get_free_variables"):
        print("Error: ts.init is not a parsed formula; please ensure the input file is in VMT format.")
        return
    if not hasattr(ts.trans, "get_free_variables"):
        print("Error: ts.trans is not a parsed formula; please ensure the input file is in VMT format.")
        return
    if not hasattr(prop, "get_free_variables"):
        print("Error: property is not a parsed formula; please ensure the input file is in VMT format.")
        return

    # Try to parse an extra demonstration formula only if 'i__AT0' is among the state variable names.
    state_names = {v.symbol_name() for v in ts.state_vars}
    if "i__AT0" in state_names:
        extra_formula = "(<= i__AT0 2)"
        try:
            f_extra = fromStringFormula(ts, extra_formula)
            print("Extra formula parsed as:", f_extra)
        except Exception as e:
            print("Skipping extra formula demonstration due to parse error:", e)
    else:
        print("Skipping extra formula demonstration: 'i__AT0' not found in state variables.")

    if not use_induction:
        # Plain BMC.
        found_cex = False
        for i in range(0, k + 1):
            f_bmc = rename_f(ts, ts.init, 0)
            for j in range(0, i):
                f_bmc = And(f_bmc, rename_f(ts, ts.trans, j))
            f_bmc = And(f_bmc, Not(rename_f(ts, prop, i)))

            print("BMC check at bound %d:" % i)
            with Solver() as solver:
                solver.add_assertion(f_bmc)
                if solver.solve():
                    print("Counterexample found at bound %d" % i)
                    model = solver.get_model()
                    print(model)
                    found_cex = True
                    break
                else:
                    print("No counterexample found at bound %d" % i)
        if not found_cex:
            print("No counterexample found up to bound %d" % k)
    else:
        # Induction branch.
        base_ok = True
        for i in range(0, k + 1):
            f_base = rename_f(ts, ts.init, 0)
            for j in range(0, i):
                f_base = And(f_base, rename_f(ts, ts.trans, j))
            f_base = And(f_base, Not(rename_f(ts, prop, i)))
            print("Induction Base Check at bound %d:" % i)
            with Solver() as solver:
                solver.add_assertion(f_base)
                if solver.solve():
                    print("Base case counterexample found at bound %d" % i)
                    model = solver.get_model()
                    print(model)
                    base_ok = False
                    break
                else:
                    print("No base case counterexample at bound %d" % i)
        if not base_ok:
            print("Property fails in the base case. Induction cannot be applied.")
            return

        # Inductive Step Check.
        f_ind = TRUE()
        for i in range(0, k + 1):
            f_ind = And(f_ind, rename_f(ts, prop, i))
        for i in range(0, k + 1):
            f_ind = And(f_ind, rename_f(ts, ts.trans, i))
        f_ind = And(f_ind, simple_path_formula(ts, k))
        f_ind = And(f_ind, Not(rename_f(ts, prop, k + 1)))

        print("Inductive Step Check (KIND_%d):" % k)
        with Solver() as solver:
            solver.add_assertion(f_ind)
            if solver.solve():
                print("Inductive step failed: a counterexample for the induction step was found.")
                model = solver.get_model()
                print(model)
            else:
                print("Inductive step succeeded: the property is inductive (using k-induction with a simple path condition).")


if __name__ == '__main__':
    main()
