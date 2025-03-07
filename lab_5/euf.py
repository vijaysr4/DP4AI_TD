# Simple EUF solver
#
# Implements a congruence closure algorithm using a union–find (disjoint-set)
# data structure along with a signature-based propagation for function applications.

from math import floor, ceil
import argparse
import os
import sys
import functools

from utils import get_terms, split_equalities

from pysmt.typing import BOOL, REAL, INT, Type, FunctionType
from pysmt.shortcuts import (
    is_valid,
    Solver,
    Symbol, TRUE, FALSE, get_env,
    Real, Int,
    Not, And, Or, Implies, Iff,
    Equals, Function, NotEquals,
    get_atoms
)
from pysmt.logics import QF_LRA


class EGraph():
    """
    Graph used to compute the congruence closure.
    It uses a union–find structure where each node is an instance of EGraph.ENode.
    """

    class ENode:
        """
        Node of the graph.
        Each node corresponds to a term.
        """

        def __init__(self, term, term_id, args):
            self.id = term_id  # unique identifier
            self.term = term  # the term (variable or function application)
            self.args = args  # list of child nodes (if any)
            self.find = term_id  # pointer used in union-find (initially self)
            # eq_parents is not used in this version, as we use signature propagation.
            self.eq_parents = set()

        def __repr__(self):
            return "%d - %d - %s (%s) - [%s]" % (self.find, self.id,
                                                 self.term.function_name() if self.term.is_function_application() else self.term,
                                                 self.term,
                                                 ",".join([str(a.id) for a in self.args]))

    def __init__(self, terms):
        """
        Build the EGraph from a set of terms.
        Create an ENode for every term.
        For function applications, assign their children (which are already created).
        """
        self.nodes = []
        self.term_to_node = {}

        # Create a node for each term (initially with empty args)
        for term in terms:
            if term not in self.term_to_node:
                node = self.ENode(term, len(self.nodes), [])
                self.nodes.append(node)
                self.term_to_node[term] = node

        # For each node corresponding to a function application, set its args.
        for node in self.nodes:
            if node.term.is_function_application():
                new_args = []
                for arg in node.term.args():
                    child_node = self.term_to_node[arg]
                    new_args.append(child_node)
                node.args = new_args

    def node(self, node_id):
        """
        Returns the node with id equal to node_id.
        """
        return self.nodes[node_id]

    def find(self, node_id):
        """
        Find the representative of the equivalence class for node_id,
        using path compression.
        """
        node = self.nodes[node_id]
        if node.find != node.id:
            node.find = self.find(node.find)
        return node.find

    def union(self, id1, id2):
        """
        Unify the equivalence classes of the two nodes.
        Returns True if a merge was performed.
        """
        rep1 = self.find(id1)
        rep2 = self.find(id2)
        if rep1 != rep2:
            self.nodes[rep1].find = rep2
            return True
        return False

    def merge_equalities(self, equalities):
        """
        Process a list of equality atoms.
        For each equality, merge the nodes corresponding to its two terms.
        """
        for eq in equalities:
            left = eq.args()[0]
            right = eq.args()[1]
            if left in self.term_to_node and right in self.term_to_node:
                self.union(self.term_to_node[left].id, self.term_to_node[right].id)

    def propagate(self):
        """
        Propagate congruence closure by merging function application nodes
        that have the same signature (function symbol and equivalence classes of arguments).
        Repeat until no further merges occur.
        """
        changed = True
        while changed:
            changed = False
            table = {}
            # Process all nodes that represent function applications.
            for node in self.nodes:
                if node.term.is_function_application():
                    # Build the signature: function name and the current reps of each argument.
                    sig = (node.term.function_name(), tuple(self.find(child.id) for child in node.args))
                    if sig in table:
                        # If a node with the same signature exists, merge the current node with it.
                        if self.union(node.id, table[sig]):
                            changed = True
                    else:
                        table[sig] = self.find(node.id)

    def check_consistency(self, inequalities):
        """
        Check if any inequality is violated.
        For each inequality (a negated equality), if the two sides have the same representative,
        then the formula is inconsistent.
        """
        for ineq in inequalities:
            left = ineq.args()[0]
            right = ineq.args()[1]
            if left in self.term_to_node and right in self.term_to_node:
                if self.find(self.term_to_node[left].id) == self.find(self.term_to_node[right].id):
                    return False
        return True


def euf_solver(formula):
    """
    Assume formula to be a conjunction of literals, and each literal has
    an equality as atom.
    The terms in the equalities should be function applications or "variables".

    Returns True if the formula is satisfiable and False otherwise.
    """
    # Extract all terms.
    terms = get_terms(formula)
    # Split the formula into equalities and inequalities.
    (equalities, inequalities) = split_equalities(formula)

    # Build the EGraph.
    graph = EGraph(terms)

    # Merge equalities.
    graph.merge_equalities(equalities)
    # Propagate congruence closure.
    graph.propagate()

    # Check if any inequality is violated.
    sat = graph.check_consistency(inequalities)
    return sat


def main():
    print("This is the EUF solver module. Use test_solver.py to run tests.")


if __name__ == '__main__':
    main()
