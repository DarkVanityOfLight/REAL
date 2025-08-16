from typing import Callable, Mapping, Set, Tuple, Union, cast, Dict

from pysmt.fnode import FNode
import pysmt.typing as typ
import pysmt.operators as operators
from pysmt.operators import EQUALS, NOT,SYMBOL
from pysmt.shortcuts import Int, Plus, Symbol, Times, get_env

from ramsey_extensions.fnode import ExtendedFNode
from ramsey_extensions.formula import ExtendedFormulaManager
from ramsey_extensions.operators import MOD_NODE_TYPE
from ramsey_extensions.shortcuts import Mod

def _vector(name: str, length: int, T: typ.PySMTType):
    return [Symbol(f"{name}_{i}", T) for i in range(length)]

def real_vector(name: str, length: int):
    return _vector(name, length, typ.REAL)
def bool_vector(name: str, length: int):
    return _vector(name, length, typ.BOOL)
def int_vector(name: str, length: int):
    return _vector(name, length, typ.INT)

def is_atom(atom: FNode) -> bool:
    """
    Check if the given node is an atom, that is an equation of the form
    ... ~ ... with ~ in { =, <, > }
    """
    return atom.get_type() == typ.BOOL and (atom.node_type() in operators.IRA_RELATIONS or atom.node_type() == operators.EQUALS)

def ensure_mod(node: ExtendedFNode, modulus: int) -> ExtendedFNode:
    if node.node_type() == MOD_NODE_TYPE and node.arg(1).constant_value() == modulus:
        return node
    else:
        # wrap it as (node % modulus)
        return Mod(node, Int(modulus))

def collect_atoms(formula: ExtendedFNode) -> Tuple[Tuple[ExtendedFNode, ...], Tuple[ExtendedFNode, ...], Tuple[ExtendedFNode, ...]]:
    """Collect all atoms, returning (equalities, modequalities, inequalities)."""

    eqs: Set[ExtendedFNode] = set()
    modeqs: Set[ExtendedFNode] = set()
    ineqs: Set[ExtendedFNode] = set()

    stack = [formula]
    while stack:
        sub = stack.pop()
        match sub.node_type():
            case t if t == EQUALS:
                if sub.arg(0).node_type() == MOD_NODE_TYPE:
                    modeqs.add(sub)
                else:
                    eqs.add(sub)
            case t if t == operators.LT or t == operators.LE:
                ineqs.add(sub)
            case t if t == NOT:
                # A mod equality can appear negated, since we can not rewrite it
                # we then treat the whole thing(negation + equation) as the actuall atom
                modeqs.add(sub)
            case _:
                # non-atom / other connective: dive into its children
                stack.extend(sub.args())

    return tuple(eqs), tuple(modeqs), tuple(ineqs)

def reconstruct_from_coeff_map(
    m: Mapping[ExtendedFNode, Union[int, float]],
    constant: Union[int, float],
    num_ctor: Callable[[Union[int, float]], ExtendedFNode]
) -> ExtendedFNode:
    terms = []
    for var, coeff in m.items():
        if coeff == 0:
            continue
        terms.append(var if coeff == 1 else Times(num_ctor(coeff), var))
    if constant != 0:
        terms.append(num_ctor(constant))

    if not terms:
        return num_ctor(0)
    if len(terms) == 1:
        return terms[0]
    return Plus(terms)

def map_atoms(formula: ExtendedFNode, f) -> ExtendedFNode:
    """ Walk over the formula, preserve its logical structure and apply f to the atoms"""
    if is_atom(formula):
        return f(formula)
    else:
        args = tuple(map_atoms(arg, f) for arg in formula.args())
        return create_node(formula.node_type(), args, formula._content.payload) 

def create_node(node_type, args, payload=None) -> ExtendedFNode:
    mngr = cast(ExtendedFormulaManager, get_env().formula_manager)

    if node_type == SYMBOL:
        return Symbol(payload[0], payload[1])

    return mngr.create_node(node_type, args, payload)

def combine_term_dict(dict1: Dict[ExtendedFNode, int], dict2: Dict[ExtendedFNode, int]):
    return {k: v + dict2.get(k, 0) for k, v in dict1.items()} | {k: v for k, v in dict2.items() if k not in dict1}

def ast_to_terms(node: ExtendedFNode
    ) -> Tuple[Dict[ExtendedFNode, Union[int, float]], Union[int, float]]:
    """
    Convert an AST representing a linear numeric expression into a mapping
    of symbolic terms to coefficients and a constant term.

    Returns:
        Tuple[Dict[ExtendedFNode, Union[int,float]], Union[int,float]]: 
        mapping from symbol -> coeff (int or float), plus the constant.
    """
    def process(n: ExtendedFNode
        ) -> Tuple[Dict[ExtendedFNode, Union[int, float]], Union[int, float]]:
        T = n.node_type()
        match T:
            case operators.INT_CONSTANT | operators.REAL_CONSTANT:
                return {}, n.constant_value()  # constant_value() is int or float

            case operators.SYMBOL:
                assert n.symbol_type() in (typ.INT, typ.REAL)
                return {n: 1}, 0

            case operators.PLUS:
                terms: Dict[ExtendedFNode, Union[int,float]] = {}
                const: Union[int,float] = 0
                for a in n.args():
                    tmap, c = process(a)
                    const += c
                    for s, co in tmap.items():
                        terms[s] = terms.get(s, 0) + co
                return terms, const

            case operators.MINUS:
                Lm, Lc = process(n.arg(0))
                Rm, Rc = process(n.arg(1))
                terms = {**Lm}
                for s, co in Rm.items():
                    terms[s] = terms.get(s, 0) - co
                return terms, Lc - Rc

            case operators.TIMES:
                terms: Dict[ExtendedFNode, Union[int,float]] = {}
                const: Union[int,float] = 1
                for a in n.args():
                    tmap, c = process(a)
                    if tmap and terms:
                        raise ValueError("Cannot multiply two symbolic parts")
                    # scale existing terms by c
                    terms = {s: co * c for s, co in terms.items()}
                    # add new term-scaled-by-const
                    for s, co in tmap.items():
                        terms[s] = terms.get(s, 0) + co * const
                    const *= c
                return terms, const

            case _:
                raise ValueError(f"Unknown node type: {T}")

    terms, const = process(node)
    # drop zero coefficients
    return {s: c for s, c in terms.items() if c != 0}, const
