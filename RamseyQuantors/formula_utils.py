from pysmt.fnode import FNode
import pysmt.typing as typ
import pysmt.operators as operators

from RamseyQuantors.fnode import ExtendedFNode
from RamseyQuantors.formula import ExtendedFormulaManager
from RamseyQuantors.operators import MOD_NODE_TYPE
from typing import Tuple, List, Iterable, Set, cast, Dict

from pysmt.operators import EQUALS, SYMBOL, IRA_OPERATORS, PLUS, TIMES
from pysmt.shortcuts import Int, Plus, Times, get_env

def isAtom(atom: FNode) -> bool:
    """
    Check if the given node is an atom, that is an equation of the form
    ... ~ ... with ~ in { =, <, > }
    """
    return atom.get_type() == typ.BOOL and (atom.node_type() in operators.IRA_RELATIONS or atom.node_type() == operators.EQUALS)

def collect_atoms(formula: ExtendedFNode) -> Tuple[Tuple[ExtendedFNode, ...], Tuple[ExtendedFNode, ...], Tuple[ExtendedFNode, ...]]:
    """Collect all atoms, returning (equalities, modequalities, inequalities)."""


    eqs: set[ExtendedFNode] = set()
    modeqs: set[ExtendedFNode] = set()
    ineqs: set[ExtendedFNode] = set()

    stack = [formula]
    while stack:
        sub = stack.pop()
        match sub.node_type():
            case t if t == EQUALS:
                if sub.arg(0).node_type() == MOD_NODE_TYPE:
                    modeqs.add(sub)
                else:
                    eqs.add(sub)
            case t if t == operators.LT:
                ineqs.add(sub)
            case _:
                # non-atom / other connective: dive into its children
                stack.extend(sub.args())

    return tuple(eqs), tuple(modeqs), tuple(ineqs)
    

def reconstruct_from_coeff_map(m: Dict[ExtendedFNode, int], constant: int) -> ExtendedFNode:
    terms = []
    for var, coeff in m.items():
        if coeff == 0:
            continue
        # coef 1: just the variable; otherwise multiply
        terms.append(var if coeff == 1 else Times(Int(coeff), var))
    if constant != 0:
        terms.append(Int(constant))

    if not terms:
        return Int(0)
    if len(terms) == 1:
        return terms[0]
    return Plus(terms)

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
    else:
        args = tuple(apply_to_atoms(arg, f) for arg in formula.args())
        return create_node(formula.node_type(), args, formula._content.payload) 

def create_node(node_type, args, payload=None) -> ExtendedFNode:
    mngr = cast(ExtendedFormulaManager, get_env().formula_manager)
    return mngr.create_node(node_type, args, payload)
