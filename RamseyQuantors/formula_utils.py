from pysmt.fnode import FNode
import pysmt.typing as typ
import pysmt.operators as operators

from RamseyQuantors.fnode import ExtendedFNode
from RamseyQuantors.formula import ExtendedFormulaManager
from RamseyQuantors.operators import MOD_NODE_TYPE, RAMSEY_NODE_TYPE
from RamseyQuantors.shortcuts import Ramsey
from typing import Tuple, List, Iterable, Set, Optional, cast

from pysmt.operators import AND, OR, IFF, IMPLIES, NOT, EQUALS, SYMBOL, IRA_OPERATORS, PLUS, TIMES, EXISTS, FORALL
from pysmt.shortcuts import Int, And, Or, Equals, Plus, Not, Iff, Implies, Exists, ForAll, get_env


def subterm(node: FNode, vars: Iterable[FNode], keep_with: bool) -> FNode:
    """Helper: extract the sum of (multi)terms that do (or don’t) contain any of `vars`."""
    with_terms, without_terms = collect_subterms_of_var(node, vars)
    return with_terms if keep_with else without_terms


def isAtom(atom: FNode) -> bool:
    """
    Check if the given node is an atom, that is an equation of the form
    ... ~ ... with ~ in { =, <, > }
    """
    return atom.get_type() == typ.BOOL and (atom.node_type() in operators.IRA_RELATIONS or atom.node_type() == operators.EQUALS)

# TODO: Find a good way to merge with the initial simplification
def collect_atoms(formula: ExtendedFNode) -> Tuple[Tuple[ExtendedFNode, ...], Tuple[ExtendedFNode, ExtendedFNode]]:
    """Collect all atoms, as (inequalities, equalities)"""
    eqs = []
    ineqs = []

    stack = [formula]
    while stack:
        subformula = stack.pop()
        match subformula.node_type():
            case op if op in {AND, OR, IFF, IMPLIES, NOT}:
                for arg in subformula.args():
                    stack.append(arg)
            case op if op == EQUALS:
                eqs.append(subformula)
            case op if op == operators.LT:
                ineqs.append(subformula)
            case _:
                print(f"Did not handle {subformula} when collecting atoms.")

    return tuple(eqs), tuple(ineqs)
    
def restrict_to_bool(values: List[FNode]):
    """Given a list of symbols, return a formula that restricts them to integer 0 or 1"""
    return And([Or(Equals(v, Int(1)), Equals(v, Int(0))) for v in values])

def split_left_right(atom: FNode, vars1: Iterable[FNode]) -> Tuple[FNode, FNode]:
    """
    Return (side_with_vars1, side_without).  Raise if vars1 is on both or neither side.
    """
    assert isAtom(atom)
    vars1 = set(vars1)
    left, right = atom.arg(0), atom.arg(1)

    # helper to collect all symbol-nodes in a subtree
    def collect_vars(node: FNode, acc: Set[FNode]):
        if node.node_type() == SYMBOL:
            acc.add(node)
        elif node.node_type() in IRA_OPERATORS or node.node_type() == MOD_NODE_TYPE:
            for c in node.args():
                collect_vars(c, acc)
        # else: constants/literals etc.

    left_syms, right_syms = set(), set()
    collect_vars(left, left_syms)
    collect_vars(right, right_syms)

    left_hits  = left_syms  & vars1
    right_hits = right_syms & vars1

    if left_hits and not right_hits:
        return left, right
    if right_hits and not left_hits:
        return right, left

    # no hits or ambiguous
    raise Exception(
        f"vars1={sorted(vars1)} found on both sides "
        f"({sorted(left_hits)} | {sorted(right_hits)}) "
        f"for atom: {atom}"
    )


def collect_subterms_of_var(
    term: FNode,
    vars: Iterable[FNode]
) -> Tuple[FNode, FNode]:
    """
    Walk a normal-form term and split its multiplicative subterms into
    those that contain any of `vars` and those that contain none.
    Returns (with_terms, without_terms), each either a Plus(...) or None.
    """
    varset = set(vars)
    with_terms: List[FNode] = []
    without_terms: List[FNode] = []
    stack: List[FNode] = [term]

    while stack:
        node = stack.pop()

        if node.node_type() == PLUS:
            # Flatten plus-nodes
            stack.extend(node.args())

        elif node.node_type() == TIMES:
            # Check if this product has any of our vars
            has_var = any(arg in varset for arg in node.args())
            if has_var:
                with_terms.append(node)
            else:
                without_terms.append(node)

        else:
            # Leaf node (constant or single var)
            is_var = node in varset
            if is_var:
                with_terms.append(node)
            else:
                without_terms.append(node)

    return (
        Plus(with_terms) if with_terms else Int(0),
        Plus(without_terms) if without_terms else Int(0)
    )


def apply_to_atoms(formula: ExtendedFNode, f) -> ExtendedFNode:
    """ Walk over the formula, preserve its logical structure and apply f to the atoms"""

    if isAtom(formula):
        
        return f(formula)
    
    match formula.node_type():
        case op if op == AND:
           return And([apply_to_atoms(subformula, f) for subformula in formula.args()]) 
        case op if op == OR:
           return And([apply_to_atoms(subformula, f) for subformula in formula.args()]) 
        case op if op == NOT:
            return Not(apply_to_atoms(formula.arg(0), f))
        case op if op == IFF:
            return Iff(apply_to_atoms(formula.arg(0), f), apply_to_atoms(formula.arg(1), f))
        case op if op == IMPLIES:
            return Implies(apply_to_atoms(formula.arg(0), f), apply_to_atoms(formula.arg(1), f))
        case op if op == EXISTS:
            return Exists(formula.quantifier_vars(), apply_to_atoms(formula.arg(0), f))
        case op if op == FORALL:
            return ForAll(formula.quantifier_vars(), apply_to_atoms(formula.arg(0), f))
        case op if op == RAMSEY_NODE_TYPE:
            return Ramsey(formula.quantifier_vars()[0], formula.quantifier_vars()[1], apply_to_atoms(formula.arg(0), f))
    
    raise Exception(f"Unhandled node type {formula}")
    

def create_node(node_type, args, payload=None):
    mngr = cast(ExtendedFormulaManager, get_env().formula_manager)
    return mngr.create_node(node_type, args, payload)
