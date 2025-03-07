# Representation of a transition system
# Mainly used to export in vmt.
#

from functools import partial
from io import StringIO
import logging

import pysmt.smtlib.commands as smtcmd
from pysmt.smtlib.script import smtlibscript_from_formula
from pysmt.smtlib.script import SmtLibScript, SmtLibCommand
from pysmt.logics import QF_NRA
from pysmt.environment import get_env
from pysmt.smtlib.annotations import Annotations
from pysmt.smtlib.printers import SmtPrinter, SmtDagPrinter, quote
from pysmt.smtlib.parser import SmtLibParser, get_formula
from pysmt.shortcuts import (
    TRUE, FALSE, Iff, And, Or, Not,
    EqualsOrIff,
    Symbol, substitute,
)
from pysmt.typing import BOOL

from formula_utils import FormulaHelper

class TS:
    """
    Transition system representation using first-order-logic formulas.
    """
    def __init__(self, env, state_vars, next_f, init, trans):
        """ Initialize a transition system """
        self.env = env
        self.init = init
        self.next_f = next_f
        self.trans = trans
        self.state_vars = set(state_vars)

    def copy_ts(self):
        """
        Copy a transition system
        """
        next_f_map = {}
        for v in self.state_vars:
            next_f_map[v] = self.next_f(v)

        next_f = lambda x : partial(substitute,
                                    subs = next_f_map)(formula = x)
        return TS(self.env, self.state_vars, next_f, self.init, self.trans)

    def to_vmt(self, outstream, safety_property):
        """
        Dump the transition system in VMT format
        """

        # compute next
        printer = SmtDagPrinter(outstream)
        cmds = []
        cmds.append(SmtLibCommand(name=smtcmd.SET_LOGIC,args=[QF_NRA]))

        # Declare all types
        for formula in [self.init, self.trans]:
            types = get_env().typeso.get_types(formula, custom_only=True)
            for type_ in types:
                cmds.append(SmtLibCommand(name=smtcmd.DECLARE_SORT, args=[type_.decl]))

        # Declare all variables
        nvcount=0
        visited = set()
        for formula in [self.init, self.trans]:
            deps = formula.get_free_variables()
            # Declare all variables
            for symbol in deps:
                if not symbol in visited:
                    visited.add(symbol)
                    assert symbol.is_symbol()
                    if not symbol in self.state_vars:
                        cmds.append(SmtLibCommand(name=smtcmd.DECLARE_FUN, args=[symbol]))

        for symbol in self.state_vars:
            cmds.append(SmtLibCommand(name=smtcmd.DECLARE_FUN, args=[symbol]))

            nv_name = "nvdef_%d" % nvcount
            nvcount = nvcount + 1
            next_s = self.next_f(symbol)

            cmds.append(SmtLibCommand(name=smtcmd.DECLARE_FUN, args=[next_s]))
            visited.add(next_s)

            cmds.append("(define-fun %s () %s (! %s :next %s))\n" %
                        (nv_name, symbol.symbol_type(),
                         symbol, self.next_f(symbol)))

        # Assert formulas
        for cmd in cmds:
            if isinstance(cmd, str):
                outstream.write(cmd)
            else:
                cmd.serialize(outstream=outstream)
            outstream.write("\n")

        def print_formula(outstream, printer, def_name, annotation, formula,
                          annotation_value = "true"):
            outstream.write("(define-fun %s () Bool (! " % def_name)
            printer.printer(formula)
            outstream.write(" :%s %s))\n" % (annotation,
                                             annotation_value))

        print_formula(outstream, printer, ".init", "init", self.init)
        print_formula(outstream, printer, ".trans", "trans", self.trans)
        print_formula(outstream, printer, ".invar-property", "invar-property",
                      safety_property, "0")
        outstream.flush()
        return



    @staticmethod
    def from_vmt(instream, env=get_env()):
        """
        Parse a transition system from VMT
        """
        parser = SmtLibParser(env)
        script = parser.get_script(instream)

        # read next
        state_vars = []
        next_f_map = {}
        state_vars = script.annotations.all_annotated_formulae("next")

        for s in state_vars:
            next_vars_str_list = script.annotations.annotations(s)["next"]
            assert((not next_vars_str_list is None) and len(next_vars_str_list) == 1)
            next_var_str = next(iter(next_vars_str_list))
            next_var = env.formula_manager.Symbol(next_var_str, s.symbol_type())
            next_f_map[s] = next_var
        next_f = lambda f : next_f_map[f]

        # TODO: fix input variables (that may not have a next in the vmt format?)

        def get_formula(script, label):
            formula = script.annotations.all_annotated_formulae(label)
            assert((not formula is None) and len(formula) == 1)
            return next(iter(formula))

        init_f = get_formula(script, "init")
        trans_f = get_formula(script, "trans")
        # May be more --- now ignore them
        safe_f = get_formula(script, "invar-property")

        return (TS(env, state_vars, next_f, init_f, trans_f), safe_f)

    @staticmethod
    def get_next_f(vars_list, env):
        next_f = lambda x : partial(FormulaHelper.rename_formula,
                                    env = env,
                                    vars = vars_list,
                                    suffix = "_next")(formula=x)
        return next_f


# EOC TS
