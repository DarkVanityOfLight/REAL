from pysmt.fnode import FNode
import pysmt.typing as typ
import pysmt.operators as operators

from RamseyQuantors.fnode import ExtendedFNode
from RamseyQuantors.formula import ExtendedFormulaManager
from RamseyQuantors.operators import MOD_NODE_TYPE
from typing import Tuple, cast, Dict

from pysmt.operators import EQUALS, NOT, PLUS, MINUS, SYMBOL, TIMES
from pysmt.shortcuts import Int, Plus, Symbol, Times, get_env

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
            case t if t == NOT:
                # A mod equality can appear negated, since we can not rewrite it
                # we then treat the whole thing(negation + equation) as the actuall atom
                modeqs.add(sub)
            case _:
                # non-atom / other connective: dive into its children
                stack.extend(sub.args())

    return tuple(eqs), tuple(modeqs), tuple(ineqs)
    
def collect_sum_terms(
    term: ExtendedFNode
) -> Tuple[Dict[ExtendedFNode, int], int]:
    """
    Flattens a sum/difference tree and returns:
      - coefficients: a dict mapping each non-constant subterm to its net integer coefficient
      - constant_term: the sum of all standalone integer literals

    Example:
      collect_sum_terms( 5*x - 3*a + 7 )  ==>  ({x:5, a:-3}, 7)
    """

    coefficients: Dict[ExtendedFNode, int] = {}
    constant_term = 0

    def _add_term(core: ExtendedFNode, coeff: int):
        nonlocal constant_term
        # If it's a pure integer literal, fold into constant_term
        if core.is_int_constant():
            constant_term += coeff * core.constant_value()
        else:
            # Otherwise accumulate into the dict
            coefficients[core] = coefficients.get(core, 0) + coeff

    def recurse(node: ExtendedFNode, sign: int):
        """sign is +1 or -1 depending on whether we're under a MINUS."""
        nt = node.node_type()

        if nt == PLUS:
            for c in node.args():
                recurse(c, sign)

        elif nt == MINUS:
            a, b = node.args()
            recurse(a, sign)      # + a
            recurse(b, -sign)     # - b

        else:
            # Leaf summand: maybe a product with an int coeff
            coeff, rest_factors = 1, []  # we'll pull out any integer literal
            if nt == TIMES:
                for arg in node.args():
                    if arg.is_int_constant():
                        coeff *= arg.constant_value()
                    else:
                        rest_factors.append(arg)
            else:
                rest_factors = [node]

            # If there were multiple non-const factors, re-make a TIMES; else take the single factor.
            if len(rest_factors) == 0:
                # pure constant times => just treat via _add_term
                _add_term(Int(1), sign * coeff)
            elif len(rest_factors) == 1:
                core = rest_factors[0]
                _add_term(core, sign * coeff)
            else:
                core = Times(rest_factors)
                _add_term(core, sign * coeff)

    recurse(term, 1)
    return coefficients, constant_term

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

def apply_to_atoms(formula: ExtendedFNode, f) -> ExtendedFNode:
    """ Walk over the formula, preserve its logical structure and apply f to the atoms"""
    if isAtom(formula):
        return f(formula)
    else:
        args = tuple(apply_to_atoms(arg, f) for arg in formula.args())
        return create_node(formula.node_type(), args, formula._content.payload) 

def create_node(node_type, args, payload=None) -> ExtendedFNode:
    mngr = cast(ExtendedFormulaManager, get_env().formula_manager)

    if node_type == SYMBOL:
        print(f"Creating symbol {payload}")
        return Symbol(payload[0], payload[1])

    return mngr.create_node(node_type, args, payload)
