from typing import List, Mapping, Tuple, cast
from pysmt import typing
from pysmt.fnode import FNode
from pysmt.shortcuts import LT, And, Equals, FreshSymbol, Int, Plus
from pysmt.typing import INT, PySMTType, _IntType, _RealType
import pysmt.operators as operators

from ramsey_elimination.simplifications import arithmetic_solver
from ramsey_extensions.fnode import ExtendedFNode
from ramsey_extensions.shortcuts import ToInt
from ramsey_elimination.formula_utils import apply_to_atoms, ast_to_terms, collect_atoms

from math import floor, lcm
from fractions import Fraction

# FIXME: We do not deal with floors correctly when building, the arithmetic_solver will die on floors

def make_zero(symbol_type: PySMTType) -> Tuple[ExtendedFNode, ExtendedFNode]:
    symbol = FreshSymbol(symbol_type)
    match symbol_type:
        case _IntType():
            return Equals(symbol, Int(0)), symbol #type: ignore
        case _RealType():
            return Equals(symbol, Real(0)), symbol #type: ignore
        case _:
            raise Exception(f"Could not create symbol with type {symbol_type.name}")

def make_one(symbol_type: PySMTType) -> Tuple[ExtendedFNode, ExtendedFNode]:
    symbol = FreshSymbol(symbol_type)
    match symbol_type:
        case _IntType():
            return Equals(symbol, Int(1)), symbol #type: ignore
        case _RealType():
            return Equals(symbol, Real(1)), symbol #type: ignore
        case _:
            raise Exception(f"Could not create symbol with type {symbol_type.name}")

def make_plus_equals(x, y, z) -> ExtendedFNode:
    return Equals(Plus(x, y), z) #type: ignore

def make_floor(x, y) -> ExtendedFNode:
    return Equals(x, ToInt(y)) #type: ignore

def make_powers_by_doubling(base: ExtendedFNode, count: int, symbol_type: PySMTType) -> Tuple[List[ExtendedFNode], List[ExtendedFNode]]:
    """
    Build [base, 2*base, 4*base, ...] up to `count` elements.
    Returns (powers_list, constraints_to_construct_them).
    """
    constraints: List[ExtendedFNode] = []
    powers = [base]
    for k in range(1, count):
        pk = cast(ExtendedFNode, FreshSymbol(symbol_type))
        constraints.append(make_plus_equals(powers[k-1], powers[k-1], pk))
        powers.append(pk)
    return powers, constraints

def sum_selected_from_zero(bits: str, elements: List[ExtendedFNode], zero: ExtendedFNode, symbol_type: PySMTType) -> Tuple[ExtendedFNode, List[ExtendedFNode]]:
    """
    Sum the elements selected by LSB-first `bits` starting from `zero`.
    Returns (sum_symbol, constraints).
    If no bit is 1, returns zero.
    """
    constraints: List[ExtendedFNode] = []
    sum_var = zero
    for i, bit in enumerate(bits):
        if bit == "1":
            tmp = cast(ExtendedFNode, FreshSymbol(symbol_type))
            constraints.append(make_plus_equals(sum_var, elements[i], tmp))
            sum_var = tmp
    return sum_var, constraints



def make_constant_int(n: int) -> Tuple[ExtendedFNode, List[ExtendedFNode]]:
    """
    Builds constraints to represent any integer n using primitives:
      x = 0, x = 1, x + y = z
    Returns (symbol_representing_n, constraints)
    """
    # Special-case zero
    if n == 0:
        c0, var0 = make_zero(INT)
        return var0, [c0]

    constraints: List[ExtendedFNode] = []

    # Ensure 1 and 0 are available (we'll need both for construction)
    c1, one = make_one(INT)
    c0, var0 = make_zero(INT)
    constraints.extend([c1, c0])

    abs_n = abs(n)

    # positive construction
    if abs_n == 1:
        positive_val = one
    else:
        bits = bin(abs_n)[2:][::-1]  # LSB-first
        # powers p[0]=1, p[1]=2, ...
        p, p_constraints = make_powers_by_doubling(one, len(bits), INT)
        constraints.extend(p_constraints)

        positive_val, sum_constraints = sum_selected_from_zero(bits, p, var0, INT)
        constraints.extend(sum_constraints)

    # if n >= 0 return positive_val
    if n > 0:
        return positive_val, constraints

    # n < 0 -> create negative by: neg + positive_val = 0
    negative_val = cast(ExtendedFNode, FreshSymbol(INT))
    constraints.append(make_plus_equals(negative_val, positive_val, var0))
    return negative_val, constraints


# FIXME: Correct the new variable type
def make_const_mul_var(a: int, x: ExtendedFNode, symbol_type: PySMTType) -> Tuple[ExtendedFNode, List[ExtendedFNode]]:
    """
    Build constraints and a fresh variable representing a * x using doubling + additions.
    Returns (symbol_for_a_times_x, constraints).
    """
    constraints: List[ExtendedFNode] = []

    # zero helper
    c0, zero = make_zero(symbol_type)
    constraints.append(c0)

    # trivial cases
    if a == 0:
        return zero, constraints
    if abs(a) == 1:
        if a > 0:
            return x, constraints
        # a == -1  => neg + x = 0
        neg = cast(ExtendedFNode, FreshSymbol(symbol_type))
        constraints.append(make_plus_equals(neg, x, zero))
        return neg, constraints

    abs_a = abs(a)
    bits = bin(abs_a)[2:][::-1]  # LSB-first

    # build multiples m[0]=x, m[1]=2*x, m[2]=4*x, ...
    m, m_constraints = make_powers_by_doubling(x, len(bits), symbol_type)
    constraints.extend(m_constraints)

    # sum selected multiples into sum_var starting from zero
    sum_var, sum_constraints = sum_selected_from_zero(bits, m, zero, symbol_type)
    constraints.extend(sum_constraints)

    if a > 0:
        return sum_var, constraints

    # a < 0 => neg + sum_var = 0
    neg = cast(ExtendedFNode, FreshSymbol(INT))
    constraints.append(make_plus_equals(neg, sum_var, zero))
    return neg, constraints


def make_atom_input_format(atom: ExtendedFNode, vars) -> Tuple[ExtendedFNode, List[ExtendedFNode]]:
    """
    Deconstructs an arithmetic atom (e.g., a*x + b*y <= c) into a canonical atom
    plus any additional constraints needed to build it using the primitives:
    x=0, x=1, x+y=z, and x<0.

    Returns:
        (new_atom, additional_constraints)
    """
    left, right = atom.arg(0), atom.arg(1)
    l_coeffs, l_const = ast_to_terms(left)
    r_coeffs, r_const = ast_to_terms(right)

    # Normalize to: sum(coeffs * var) ~ c
    coeffs, _, c = arithmetic_solver(l_coeffs, l_const, r_coeffs, r_const, vars)

    # Scale coefficients to integers
    l_c_m = 1
    for _, coeff in coeffs:
        frac_coeff = Fraction(coeff).limit_denominator()
        if frac_coeff.denominator != 1:
            l_c_m = lcm(frac_coeff.denominator, l_c_m)

    scaled_coeffs = [
        (var, int(Fraction(coeff).limit_denominator() * l_c_m))
        for var, coeff in coeffs
    ]
    scaled_c = int(Fraction(c).limit_denominator() * l_c_m)

    constraints = []

    # 1. Build LHS from variables
    term_symbols = []
    for var, coeff in scaled_coeffs:
        term_symbol, mul_atoms = make_const_mul_var(coeff, var, var.symbol_type())
        constraints.extend(mul_atoms)
        term_symbols.append(term_symbol)

    if not term_symbols:
        zero_atom, lhs_symbol = make_zero(INT)
        constraints.append(zero_atom)
        sum_typ = INT
    else:
        current_sum = term_symbols[0]
        sum_typ = term_symbols[0].symbol_type()
        for i in range(1, len(term_symbols)):
            sum_result_symbol = FreshSymbol(sum_typ)
            plus_atom = make_plus_equals(current_sum, term_symbols[i], sum_result_symbol)
            constraints.append(plus_atom)
            current_sum = sum_result_symbol
        lhs_symbol = current_sum

    # 2. Build RHS constant
    const_symbol, const_atoms = make_constant_int(scaled_c)
    constraints.extend(const_atoms)

    # 3. diff = LHS - RHS
    neg_const_symbol, neg_const_atoms = make_const_mul_var(-1, const_symbol, const_symbol.symbol_type())
    constraints.extend(neg_const_atoms)

    diff_symbol = FreshSymbol(sum_typ)
    diff_atom = make_plus_equals(lhs_symbol, neg_const_symbol, diff_symbol)
    constraints.append(diff_atom)

    # 4. Canonical constants
    zero_atom, zero_symbol = make_zero(sum_typ)
    one_atom, one_symbol = make_one(sum_typ)
    constraints.extend([zero_atom, one_atom])

    # 5. Create main canonical atom
    match atom.node_type():
        case operators.EQUALS:
            # diff = 0
            main_atom = make_plus_equals(diff_symbol, zero_symbol, zero_symbol)
        case operators.LT:
            # diff < 0
            main_atom = cast(ExtendedFNode, LT(diff_symbol, zero_symbol))
        case operators.LE:
            # diff <= 0 → diff < 1
            main_atom = cast(ExtendedFNode, LT(diff_symbol, one_symbol))
        case _:
            raise Exception(f"Unkown relation {atom.node_type()}")

    return main_atom, constraints


def make_input_format(f, vars):
    additional_constraints = []

    def collector(atom):
        new_atom, constraints = make_atom_input_format(atom, vars) 
        additional_constraints.extend(constraints)
        return new_atom

    new_f = apply_to_atoms(f, collector)
    
    return And(new_f, *additional_constraints)


def rewrite_atom(coefficient_map: Mapping[str, float], constant: float):
    pass

def input_format():
    pass
