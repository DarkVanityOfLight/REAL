from pysmt.fnode import FNode
import pysmt.typing as typ
import pysmt.operators as operators

from RamseyQuantors.fnode import ExtendedFNode
from RamseyQuantors.formula import ExtendedFormulaManager
from RamseyQuantors.operators import MOD_NODE_TYPE
from typing import Tuple, cast, Dict

from pysmt.operators import EQUALS, INT_CONSTANT, NOT, PLUS, MINUS, SYMBOL, TIMES
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
        return Symbol(payload[0], payload[1])

    return mngr.create_node(node_type, args, payload)

def combine_term_dict(dict1: Dict[ExtendedFNode, int], dict2: Dict[ExtendedFNode, int]):
    return {k: v + dict2.get(k, 0) for k, v in dict1.items()} | {k: v for k, v in dict2.items() if k not in dict1}

def ast_to_terms(node: ExtendedFNode):
    """
    Convert an AST representing a linear integer expression into a mapping
    of symbolic terms to coefficients and a constant term.

    Args:
        node (ExtendedFNode): Root of the AST to process.

    Returns:
        Tuple[Dict[ExtendedFNode, int], int]: A pair (terms, constant) where `terms` maps
        each symbolic node to its integer coefficient, and `constant` is the summed
        integer constant.
    """
    def process(n: ExtendedFNode) -> Tuple[Dict[ExtendedFNode, int], int]:
        T = n.node_type()
        match T:
            case operators.INT_CONSTANT:
                # For integer constants, no symbolic terms, just return its value
                return ({}, n.constant_value())

            case operators.SYMBOL:
                # Symbols represent variables; assume integer type
                assert n.symbol_type() == typ.INT
                # Return a single-term map: this symbol has coefficient 1
                return ({n: 1}, 0)

            case operators.PLUS:
                # Handle addition: sum up terms and constants from all operands
                combined_terms: Dict[ExtendedFNode, int] = {}
                combined_const: int = 0

                for term in n.args():
                    term_terms, term_const = process(term)
                    # Accumulate constant parts
                    combined_const += term_const
                    # Merge symbolic terms, adding coefficients
                    for sym, coeff in term_terms.items():
                        combined_terms[sym] = combined_terms.get(sym, 0) + coeff
                return (combined_terms, combined_const)

            case operators.MINUS:
                left_terms, left_const = process(n.arg(0))
                right_terms, right_const = process(n.arg(1))

                combined_terms = {}

                for sym, coeff in left_terms.items():
                    combined_terms[sym] = coeff

                for sym, coeff in right_terms.items():
                    if sym in combined_terms:
                        combined_terms[sym] -= coeff
                    else:
                        combined_terms[sym] = -coeff
                return (combined_terms, left_const - right_const)


            case operators.TIMES:
                # Handle multiplication: only allow one symbolic factor
                product_terms: Dict[ExtendedFNode, int] = {}
                product_const: int = 1

                for term in n.args():
                    term_terms, term_const = process(term)
                    # Disallow multiplication of two non-constant expressions
                    if term_terms and product_terms:
                        raise ValueError(
                            "Invalid multiplication of two non-constant expressions"
                        )
                    # Scale existing symbolic terms by the new constant
                    new_terms: Dict[ExtendedFNode, int] = {}
                    for sym, coeff in product_terms.items():
                        new_terms[sym] = coeff * term_const

                    # Introduce new symbolic terms scaled by the accumulated constant
                    for sym, coeff in term_terms.items():
                        new_coeff = coeff * product_const
                        new_terms[sym] = new_terms.get(sym, 0) + new_coeff

                    # Update constant multiplier
                    product_const *= term_const
                    product_terms = new_terms
                return (product_terms, product_const)

            case _:
                # Catch-all for any unrecognized node types
                raise ValueError(f"Unknown node type: {T}")

    terms, const = process(node)
    # Clean 0 coeffs
    return {s: c for s, c in terms.items() if c != 0}, const
