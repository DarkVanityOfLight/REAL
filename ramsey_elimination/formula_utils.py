from typing import Callable, List, Mapping, Optional, Set, Tuple, Union, cast, Dict

from pysmt.fnode import FNode
import pysmt.typing as typ
import pysmt.operators as operators
from pysmt.operators import EQUALS, NOT, SYMBOL, TOREAL
from pysmt.shortcuts import Int, Plus, Symbol, Times, get_env, FreshSymbol

from ramsey_extensions.fnode import ExtendedFNode
from ramsey_extensions.formula import ExtendedFormulaManager
from ramsey_extensions.operators import MOD_NODE_TYPE, TOINT_NODE_TYPE
from ramsey_extensions.shortcuts import Mod
import ramsey_extensions.operators as cops

FNode = ExtendedFNode # type: ignore[misc]

# ---------------------------------------------------------------------
# Vector constructors
# ---------------------------------------------------------------------

def _fresh_vector(template: str, length: int, T: typ.PySMTType) -> List[ExtendedFNode]:
    """Create a list of fresh symbols of the given type and length."""
    return [FreshSymbol(T, (template.format(i, "{}"))) for i in range(length)]

def fresh_real_vector(template: str, length: int):
    """Create a fresh vector of real variables."""
    return _fresh_vector(template, length, typ.REAL)

def fresh_bool_vector(template: str, length: int):
    """Create a fresh vector of boolean variables."""
    return _fresh_vector(template, length, typ.BOOL)

def fresh_int_vector(template: str, length: int):
    """Create a fresh vector of integer variables."""
    return _fresh_vector(template, length, typ.INT)


def _vector(name: str, length: int, T: typ.PySMTType) -> List[ExtendedFNode]:
    """Create a list of named symbols (name_0, name_1, ...) of a given type."""
    return [Symbol(f"{name}_{i}", T) for i in range(length)]  # type: ignore

def real_vector(name: str, length: int):
    """Create a named vector of real symbols."""
    return _vector(name, length, typ.REAL)

def bool_vector(name: str, length: int):
    """Create a named vector of boolean symbols."""
    return _vector(name, length, typ.BOOL)

def int_vector(name: str, length: int):
    """Create a named vector of integer symbols."""
    return _vector(name, length, typ.INT)


# ---------------------------------------------------------------------
# Formula classification and manipulation
# ---------------------------------------------------------------------

def is_atom(atom: ExtendedFNode) -> bool:
    """
    Check whether the given node is a Boolean atomic predicate, i.e.
    a comparison of the form (x = y), (x < y), or (x > y).
    """
    return atom.get_type() == typ.BOOL and (
        atom.node_type() in operators.IRA_RELATIONS or atom.node_type() == operators.EQUALS
    )

def ensure_mod(node: ExtendedFNode, modulus: int) -> ExtendedFNode:
    """
    Ensure that the node is a mod-expression with the given modulus.
    Wraps the node as (node % modulus) if necessary.
    """
    if node.node_type() == MOD_NODE_TYPE and node.arg(1).constant_value() == modulus:
        return node
    return Mod(node, Int(modulus))


def collect_atoms(formula: ExtendedFNode) -> Tuple[
    Tuple[ExtendedFNode, ...], Tuple[ExtendedFNode, ...], Tuple[ExtendedFNode, ...]
]:
    """
    Collect atomic subformulas from a Boolean formula.

    Returns:
        (equalities, modequalities, inequalities)
    """
    eqs: Set[ExtendedFNode] = set()
    modeqs: Set[ExtendedFNode] = set()
    ineqs: Set[ExtendedFNode] = set()

    stack = [formula]
    while stack:
        sub = stack.pop()

        if sub.is_equals():
            if contains_mod(sub):
                modeqs.add(sub)
            else:
                eqs.add(sub)

        elif sub.is_lt() or sub.is_le():
            ineqs.add(sub)

        elif sub.is_not():
            # A negated mod-equality counts as a modular equality atom
            if contains_mod(sub):
                modeqs.add(sub)

        else:
            stack.extend(sub.args())

    return tuple(eqs), tuple(modeqs), tuple(ineqs)


# ---------------------------------------------------------------------
# Linear term reconstruction and transformation
# ---------------------------------------------------------------------

def reconstruct_from_coeff_map(
    m: Mapping[ExtendedFNode, Union[int, float]],
    constant: Union[int, float],
    num_ctor: Callable[[Union[int, float]], ExtendedFNode]
) -> ExtendedFNode:
    """
    Rebuild a linear expression from a variable→coefficient mapping and a constant term.
    Example:
        {x: 2, y: -3}, 5  =>  (2*x + (-3)*y + 5)
    """
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


# ---------------------------------------------------------------------
# Structural traversal utilities
# ---------------------------------------------------------------------

def map_atoms(formula: ExtendedFNode, f) -> ExtendedFNode:
    """
    Recursively traverse a formula and apply `f` to each atomic predicate,
    preserving the logical structure of the formula.
    """
    if is_atom(formula):
        return f(formula)
    args = tuple(map_atoms(arg, f) for arg in formula.args())
    return create_node(formula.node_type(), args, formula._content.payload)


def map_arithmetic_atom(atom: ExtendedFNode, f: Callable[[ExtendedFNode], ExtendedFNode]) -> ExtendedFNode:
    """
    Recursively apply `f` to all arithmetic subterms of an atom.
    For example, transforming all variables inside (x + y < 3).
    """
    if atom.is_symbol() or atom.is_algebraic_constant():
        return f(atom)
    args = tuple(map_arithmetic_atom(arg, f) for arg in atom.args())
    return create_node(atom.node_type(), args, atom._content.payload)


def generic_recursor(formula: ExtendedFNode, f: Callable[[ExtendedFNode], Optional[ExtendedFNode]]) -> ExtendedFNode:
    """
    Generic recursive transformer:
    Applies `f` to a node; if `f` returns None, recursively continues to children.
    """
    if x := f(formula):
        return x
    args = tuple(generic_recursor(arg, f) for arg in formula.args())
    return create_node(formula.node_type(), args, formula._content.payload)


def create_node(node_type, args, payload=None) -> ExtendedFNode:
    """Wrapper for creating an ExtendedFNode through the current environment’s formula manager."""
    mngr = cast(ExtendedFormulaManager, get_env().formula_manager)
    if node_type == SYMBOL:
        assert payload
        return Symbol(payload[0], payload[1])
    return mngr.create_node(node_type, args, payload)


def combine_term_dict(dict1: Dict[ExtendedFNode, int], dict2: Dict[ExtendedFNode, int]):
    """Combine two variable -> coefficient maps by summing overlapping entries."""
    return {k: v + dict2.get(k, 0) for k, v in dict1.items()} | {
        k: v for k, v in dict2.items() if k not in dict1
    }


def ast_to_terms(node: ExtendedFNode) -> Tuple[Dict[ExtendedFNode, Union[int, float]], Union[int, float]]:
    """
    Convert a linear arithmetic AST into (coeff_map, constant).

    Example:
        3*x + 2*y - 5  ->  ({x: 3, y: 2}, -5)
    """
    def process(n: ExtendedFNode) -> Tuple[Dict[ExtendedFNode, Union[int, float]], Union[int, float]]:
        T = n.node_type()
        match T:
            case operators.INT_CONSTANT | operators.REAL_CONSTANT:
                return {}, n.constant_value()

            case operators.SYMBOL:
                assert n.symbol_type() in (typ.INT, typ.REAL)
                return {n: 1}, 0

            case operators.PLUS:
                terms: Dict[ExtendedFNode, Union[int, float]] = {}
                const: Union[int, float] = 0
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
                # Restrict to linear multiplication (constant * variable)
                terms: Dict[ExtendedFNode, Union[int, float]] = {}
                const: Union[int, float] = 1
                for a in n.args():
                    tmap, c = process(a)
                    if tmap and terms:
                        raise ValueError("Cannot multiply two symbolic parts")
                    terms = {s: co * c for s, co in terms.items()}
                    for s, co in tmap.items():
                        terms[s] = terms.get(s, 0) + co * const
                    const *= c
                return terms, const

            case operators.TOREAL | cops.TOINT_NODE_TYPE:
                return process(n.arg(0))

            case _:
                raise ValueError(f"Unknown node type: {n}")

    terms, const = process(node)
    # Remove zero coefficients
    return {s: c for s, c in terms.items() if c != 0}, const

def apply_subst(coeffs: Mapping[ExtendedFNode, Union[int, float]], subst: Mapping[ExtendedFNode, ExtendedFNode]) -> Dict[ExtendedFNode, Union[int, float]]:
    """
    Apply a substitution map to a coefficient map, keeping unmapped keys.
    """
    return {subst.get(var, var): coeff for var, coeff in coeffs.items()}

def contains_mod(node: ExtendedFNode) -> bool:
    """Check if a node contains a modulo operation anywhere in its subtree."""
    if node.node_type() == MOD_NODE_TYPE:
        return True
    for arg in node.args():
        if contains_mod(arg):
            return True
    return False
