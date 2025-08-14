from typing import List, Mapping, Tuple, cast
from pysmt.shortcuts import LT, And, Equals, FreshSymbol, Int, Plus
from pysmt.typing import INT
import pysmt.operators as operators

from ramsey_elimination.simplifications import arithmetic_solver
from ramsey_extensions.fnode import ExtendedFNode
from ramsey_extensions.shortcuts import ToInt
from ramsey_elimination.formula_utils import apply_to_atoms, ast_to_terms, collect_atoms

from math import floor, lcm
from fractions import Fraction

def make_zero() -> Tuple[ExtendedFNode, ExtendedFNode]:
    symbol = FreshSymbol(INT)
    return Equals(symbol, Int(0)), symbol #type: ignore

def make_one() -> Tuple[ExtendedFNode, ExtendedFNode]:
    symbol = FreshSymbol(INT)
    return Equals(symbol, Int(1)), symbol #type: ignore

def make_plus_equals(x, y, z) -> ExtendedFNode:
    return Equals(Plus(x, y), z) #type: ignore

def make_floor(x, y) -> ExtendedFNode:
    return Equals(x, ToInt(y)) #type: ignore

def build_constant_int(n: int) -> Tuple[ExtendedFNode, List[ExtendedFNode]]:
    """
    Builds constraints to represent any integer n
    Parameters: 
        n: The number to encode
    Returns:
        - The Variable representing the constant
        - A list of additional constraints
    """
    constraints = []

    # (i) Handle zero as a special case
    if n == 0:
        c0, var0 = make_zero()
        constraints.append(c0)
        return var0, constraints

    # Create one and zero, which are fundamental building blocks
    c1, one = make_one()
    constraints.append(c1)
    c0, var0 = make_zero()
    constraints.append(c0)

    # Work with the absolute value of n to build the positive counterpart first
    abs_n = abs(n)

    # Handle the special case where the absolute value is 1
    if abs_n == 1:
        positive_val = one
    else:
        # Bits LSB-first (skip '0b' and reverse)
        bits = bin(abs_n)[2:][::-1]

        # Build powers of two: p[0]=1, p[1]=2, p[2]=4, ...
        # This uses repeated application of x + y = z
        p = [one]
        for k in range(1, len(bits)):
            pk = cast(ExtendedFNode, FreshSymbol(INT))
            # pk = p[k-1] + p[k-1]  (e.g., 2=1+1, 4=2+2, etc.)
            constraints.append(make_plus_equals(p[k-1], p[k-1], pk))
            p.append(pk)

        # Sum the selected powers of two into `sum_var` starting from zero
        sum_var = var0
        for i, bit in enumerate(bits):
            if bit == "1":
                tmp = cast(ExtendedFNode, FreshSymbol(INT))
                # tmp = sum_var + p[i]
                constraints.append(make_plus_equals(sum_var, p[i], tmp))
                sum_var = tmp
        positive_val = sum_var

    # Now, check if the original number was negative
    if n > 0:
        # If n was positive, we're done. Return the positive value.
        return positive_val, constraints
    else: # n < 0
        # If n was negative, we need to create its negative counterpart.
        # We introduce a new variable for our target negative number.
        negative_val = cast(ExtendedFNode, FreshSymbol(INT))

        # (iii) Use the constraint x + y = z to define the negative number.
        # We assert that: negative_val + positive_val = 0
        # This forces `negative_val` to be `-n`.
        constraints.append(make_plus_equals(negative_val, positive_val, var0))

        return negative_val, constraints

def build_mul_int_var(a: int, x) -> Tuple[ExtendedFNode, List[ExtendedFNode]]:
    """
    Build constraints and a fresh variable representing a * x.
    Parameters:
        a: The coefficient
        x: The variable
    Returns:
        - The new variable representing a*x 
        - Additional constraints
    """
    constraints = []

    # zero helper
    c0, zero = make_zero()
    constraints.append(c0)

    # trivial cases
    if a == 0:
        return zero, constraints
    if abs(a) == 1:
        if a > 0:
            return x, constraints
        # a == -1
        neg = cast(ExtendedFNode, FreshSymbol(INT))
        constraints.append(make_plus_equals(neg, x, zero))  # neg + x = 0 -> neg = -x
        return neg, constraints

    abs_a = abs(a)
    bits = bin(abs_a)[2:][::-1]  # LSB-first

    # build multiples m[0]=x, m[1]=2*x, m[2]=4*x, ...
    m = [x]
    for k in range(1, len(bits)):
        mk = FreshSymbol(INT)
        constraints.append(make_plus_equals(m[k-1], m[k-1], mk))
        m.append(mk)

    # sum selected multiples into sum_var starting from zero
    sum_var : ExtendedFNode = zero
    for i, bit in enumerate(bits):
        if bit == "1":
            tmp = cast(ExtendedFNode, FreshSymbol(INT))
            constraints.append(make_plus_equals(sum_var, m[i], tmp))
            sum_var = tmp

    positive_val = sum_var

    if a > 0:
        return positive_val, constraints
    else:
        neg = cast(ExtendedFNode, FreshSymbol(INT))
        constraints.append(make_plus_equals(neg, positive_val, zero))  # neg + positive_val = 0 -> neg = -positive_val
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
        term_symbol, mul_atoms = build_mul_int_var(coeff, var)
        constraints.extend(mul_atoms)
        term_symbols.append(term_symbol)

    if not term_symbols:
        zero_atom, lhs_symbol = make_zero()
        constraints.append(zero_atom)
    else:
        current_sum = term_symbols[0]
        for i in range(1, len(term_symbols)):
            sum_result_symbol = FreshSymbol(INT)
            plus_atom = make_plus_equals(current_sum, term_symbols[i], sum_result_symbol)
            constraints.append(plus_atom)
            current_sum = sum_result_symbol
        lhs_symbol = current_sum

    # 2. Build RHS constant
    const_symbol, const_atoms = build_constant_int(scaled_c)
    constraints.extend(const_atoms)

    # 3. diff = LHS - RHS
    neg_const_symbol, neg_const_atoms = build_mul_int_var(-1, const_symbol)
    constraints.extend(neg_const_atoms)

    diff_symbol = FreshSymbol(INT)
    diff_atom = make_plus_equals(lhs_symbol, neg_const_symbol, diff_symbol)
    constraints.append(diff_atom)

    # 4. Canonical constants
    zero_atom, zero_symbol = make_zero()
    one_atom, one_symbol = make_one()
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
