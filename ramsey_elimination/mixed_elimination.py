from typing import List, Mapping, Tuple, cast
from pysmt import typing
from pysmt.fnode import FNode
from pysmt.shortcuts import GE, LT, And, Equals, FreshSymbol, Implies, Int, Minus, Plus, Real, ToReal
from pysmt.typing import INT, REAL, PySMTType, _IntType, _RealType
import pysmt.operators as operators

from ramsey_elimination.simplifications import arithmetic_solver
from ramsey_extensions.fnode import ExtendedFNode
from ramsey_extensions.shortcuts import ToInt
from ramsey_elimination.formula_utils import map_atoms, ast_to_terms, collect_atoms

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


def make_atom_input_format(atom: ExtendedFNode) -> Tuple[ExtendedFNode, List[ExtendedFNode]]:
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
    coeffs, _, c = arithmetic_solver(l_coeffs, l_const, r_coeffs, r_const, set({}))

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

def make_input_format(f):
    additional_constraints = []

    def collector(atom):
        new_atom, constraints = make_atom_input_format(atom) 
        additional_constraints.extend(constraints)
        return new_atom

    new_f = map_atoms(f, collector)
    
    return And(new_f, *additional_constraints)

def split_int_real(f):

    def atom_rewriter(atom: ExtendedFNode):
        if atom.is_symbol() and atom.get_type() == REAL:
            i = FreshSymbol(INT)
            r = FreshSymbol(REAL)
            return Plus(ToReal(i), r)
        else:
            return atom

    return map_atoms(f, atom_rewriter)


def flatten_plus(expr: FNode) -> List[FNode]:
    """Return a flat list of terms in a + b + c ... (non-recursive for other nodes)."""
    if expr.is_plus():
        out = []
        for a in expr.args():
            out.extend(flatten_plus(a))
        return out
    return [expr]

def split_by_type(terms: List[FNode]) -> Tuple[List[FNode], List[FNode], FNode]:
    """Split symbol terms into (int_syms, real_syms, const_sum).
       Assumes constants present only as Int/Real constants (or none)."""
    ints, reals = [], []
    const_sum = None
    for t in terms:
        if t.is_symbol():
            if t.symbol_type() == INT:
                ints.append(t)
            elif t.symbol_type() == REAL:
                reals.append(t)
            else:
                raise ValueError("unexpected symbol type")
        elif t.is_constant():
            const_sum = t if const_sum is None else Plus(const_sum, t)
        else:
            # for our restricted shapes we don't expect other node types
            raise ValueError("unexpected term type: %s" % t.node_type())
    if const_sum is None:
        const_sum = Int(0) if len(ints)>0 else Real(0)
    return ints, reals, const_sum

def rewrite_atom(atom: ExtendedFNode) -> FNode:
    """Detect which of the allowed shapes `atom` is and return the rewritten formula.
       Assumes atom exactly matches one of the left-hand-side shapes."""
    if not (atom.is_equals() or atom.is_lt() or atom.is_le()):
        raise ValueError("unsupported atom shape")

    # handle binary relations only
    lhs: ExtendedFNode; rhs: ExtendedFNode
    lhs, rhs = atom.args()

    # Case A,B,D,E: forms where one side is a sum of int+real and the other is constant or floor/const
    # We'll first try simple shapes: (int + real) = k  or (int + real) < 0
    def try_int_plus_real_vs_constant(a, b, rel):
        # a = plus(int, real) and b = constant int/real
        if a.is_plus():
            terms = flatten_plus(a)
            try:
                ints, reals, consts = split_by_type(terms)
            except ValueError:
                return None
            if len(ints) == 1 and len(reals) == 1 and (b.is_constant()):
                xi = ints[0]; xr = reals[0]
                # equality cases with integer constants
                if rel == "eq" and b.is_int_constant():
                    k = b  # Int(k)
                    # if k is 0 -> xi=0 and xr=0
                    # if k is 1 -> xi=1 and xr=0 (assumed fractional domain [0,1) for xr)
                    if int(str(k.constant_value())) == 0:
                        return And(Equals(xi, Int(0)), Equals(xr, Real(0)))
                    if int(str(k.constant_value())) == 1:
                        return And(Equals(xi, Int(1)), Equals(xr, Real(0)))
                # inequality case (int + real) < 0 -> int < 0
                if rel == "lt" and b.is_int_constant() and int(str(b.constant_value())) == 0:
                    return LT(xi, Int(0))
        return None

    # try both orientations
    if atom.is_equals():
        # equality
        # 1) (int+real) = 0  or = 1
        r = try_int_plus_real_vs_constant(lhs, rhs, "eq") or try_int_plus_real_vs_constant(rhs, lhs, "eq")
        if r is not None:
            return r

    if atom.is_le():
        r = try_int_plus_real_vs_constant(lhs, rhs, "lt") or try_int_plus_real_vs_constant(rhs, lhs, "lt")
        if r is not None:
            return r

    # Case C: xint + xreal + yint + yreal = zint + zreal
    # detect exact pattern: lhs has 4 symbol terms (2 ints,2 reals), rhs has 2 (1 int,1 real)
    if atom.is_equals():
        if lhs.is_plus() and rhs.is_plus():
            lhs_terms = flatten_plus(lhs)
            rhs_terms = flatten_plus(rhs)
            try:
                li, lr, _ = split_by_type(lhs_terms)
                ri, rr, _ = split_by_type(rhs_terms)
            except ValueError:
                li = lr = ri = rr = []
            if len(li) == 2 and len(lr) == 2 and len(ri) == 1 and len(rr) == 1:
                # name the symbols
                xint, yint = li[0], li[1]
                xreal, yreal = lr[0], lr[1]
                zint = ri[0]
                zreal = rr[0]
                # build R = xreal + yreal
                R = Plus(xreal, yreal)
                # case1: R < 1 -> xint + yint = zint  AND  xreal + yreal = zreal
                case1 = Implies(LT(R, Real(1)),
                                And(Equals(Plus(xint, yint), zint),
                                    Equals(R, zreal)))
                # case2: R >= 1 -> xint + yint + 1 = zint  AND  xreal + yreal - 1 = zreal
                case2 = Implies(GE(R, Real(1)),
                                And(Equals(Plus(Plus(xint, yint), Int(1)), zint),
                                    Equals(Minus(R, Real(1)), zreal)))
                return And(case1, case2)

    # Case F: xint + xreal = floor(yint + yreal)
    # We accept RHS being an application named 'floor' or 'to_int'
    if atom.is_equals():
        # lhs must be plus of int+real
        if lhs.is_plus():
            try:
                li, lr, _ = split_by_type(flatten_plus(lhs))
            except ValueError:
                li = lr = []
            if len(li) == 1 and len(lr) == 1:
                xi, xr = li[0], lr[0]
                # detect floor-like RHS:
                if rhs.is_function_application():
                    if rhs.is_toint():
                        arg = rhs.args()[0]
                        # expect arg = yint + yreal
                        if arg.is_plus():
                            try:
                                yi_list, yr_list, _ = split_by_type(flatten_plus(arg))
                            except ValueError:
                                yi_list = yr_list = []
                            if len(yi_list) == 1 and len(yr_list) == 1:
                                yi = yi_list[0]
                                # rewrite: xreal = 0 /\ xint = yi
                                return And(Equals(xr, Real(0)), Equals(xi, yi))

    raise ValueError("atom did not match any supported left-hand shape")

def decompose(f):
    return map_atoms(f, rewrite_atom)

def compute_decomposition(f):
    f_new = make_input_format(f)
    f_new = split_int_real(f)
    return decompose(f_new)
