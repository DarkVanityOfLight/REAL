from typing import List, Mapping, Optional, Tuple, cast
from pysmt import typing
from pysmt.fnode import FNode
from pysmt.shortcuts import GE, LE, LT, And, Equals, FreshSymbol, Implies, Int, Minus, Plus, Real, Symbol, Times, ToReal
from pysmt.typing import INT, REAL, PySMTType, _IntType, _RealType
import pysmt.operators as operators

from ramsey_elimination.simplifications import arithmetic_solver
from ramsey_extensions.fnode import ExtendedFNode
from ramsey_extensions.shortcuts import ToInt
from ramsey_elimination.formula_utils import generic_recursor, map_arithmetic_atom, map_atoms, ast_to_terms, collect_atoms

from math import floor, lcm
from fractions import Fraction

def make_zero(symbol_type: PySMTType) -> Tuple[ExtendedFNode, ExtendedFNode]:
    symbol = FreshSymbol(symbol_type, f"zero_{symbol_type}_%s")
    match symbol_type:
        case _IntType():
            return Equals(symbol, Int(0)), symbol #type: ignore
        case _RealType():
            return Equals(symbol, Real(0)), symbol #type: ignore
        case _:
            raise Exception(f"Could not create symbol with type {symbol_type.name}")

def make_one(symbol_type: PySMTType) -> Tuple[ExtendedFNode, ExtendedFNode]:
    symbol = FreshSymbol(symbol_type, f"one_{symbol_type}_%s")
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
        pk = cast(ExtendedFNode, FreshSymbol(symbol_type, f"2^{k}_{symbol_type}_%s"))
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
            tmp = cast(ExtendedFNode, FreshSymbol(symbol_type, f"sum_{symbol_type}%s"))
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
    negative_val = cast(ExtendedFNode, FreshSymbol(INT, "what_is_this_%s"))
    constraints.append(make_plus_equals(negative_val, positive_val, var0))
    return negative_val, constraints


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
        neg = cast(ExtendedFNode, FreshSymbol(symbol_type, f"{symbol_type}%s"))
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
    neg = cast(ExtendedFNode, FreshSymbol(symbol_type, f"{sum_var.symbol_name()}_{symbol_type}%s"))
    constraints.append(make_plus_equals(neg, sum_var, zero))
    return neg, constraints

def clean_floors(f: ExtendedFNode) -> ExtendedFNode:
    extra_constraints = []
    def _cleaner(symbol: ExtendedFNode):
        if symbol.is_toint():
            inner = FreshSymbol(REAL, f"innerfloor_%s")
            inner_constraint = Equals(inner, symbol.arg(0)) 
            outer : ExtendedFNode = FreshSymbol(INT, f"outer_floor%s") # type: ignore
            outer_constraint = Equals(outer, ToInt(inner))
            extra_constraints.extend((inner_constraint, outer_constraint))
            return outer

    return And(generic_recursor(f, _cleaner), *extra_constraints) # type: ignore

def make_atom_input_format(atom: ExtendedFNode) -> Tuple[ExtendedFNode, List[ExtendedFNode]]:
    """
    Deconstructs an arithmetic atom (e.g., a*x + b*y <= c) into a canonical atom
    plus any additional constraints needed to build it using the primitives:
    x=0, x=1, x+y=z, and x<0.

    Returns:
        (new_atom, additional_constraints)
    """
    left, right = atom.arg(0), atom.arg(1)

    if left.is_toint() or right.is_toint():
        return atom, []

    l_coeffs, l_const = ast_to_terms(left)
    r_coeffs, r_const = ast_to_terms(right)

    # Normalize to: sum(coeffs * var) ~ c
    coeffs, _, c = arithmetic_solver(l_coeffs, l_const, r_coeffs, r_const, set({}))

    # Scale coefficients to integers
    l_c_m = 1
    for coeff in coeffs.values():
        frac_coeff = Fraction(coeff).limit_denominator()
        if frac_coeff.denominator != 1:
            l_c_m = lcm(frac_coeff.denominator, l_c_m)

    scaled_coeffs = [
        (var, int(Fraction(coeff).limit_denominator() * l_c_m))
        for var, coeff in coeffs.items()
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
        sum_typ = REAL if any(s.get_type() == REAL for s in term_symbols) else INT

        def to_real_if_needed(sym):
            return ToReal(sym) if (sym.get_type() == INT and sum_typ == REAL) else sym

        current_sum = to_real_if_needed(term_symbols[0])

        for i in range(1, len(term_symbols)):
            sum_result_symbol = FreshSymbol(sum_typ)

            term_symbol = to_real_if_needed(term_symbols[i])

            plus_atom = make_plus_equals(current_sum, term_symbol, sum_result_symbol)
            constraints.append(plus_atom)
            current_sum = sum_result_symbol

        lhs_symbol = current_sum

    # 2. Build RHS constant
    const_symbol, const_atoms = make_constant_int(scaled_c)
    constraints.extend(const_atoms)
    if sum_typ == REAL:
        const_symbol_real = cast(ExtendedFNode, ToReal(const_symbol))
        const_symbol = const_symbol_real

    # 3. diff = LHS - RHS
    neg_const_symbol, neg_const_atoms = make_const_mul_var(-1, const_symbol, sum_typ)
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
            match sum_typ:
                case _IntType():
                    main_atom = cast(ExtendedFNode, LT(diff_symbol, Int(0)))
                case _RealType():
                    main_atom = cast(ExtendedFNode, LT(diff_symbol, Real(0)))
                case _:
                    raise Exception(f"Unknown type: {sum_typ}")
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
    new_reals = []
    def atom_rewriter(op: ExtendedFNode) -> ExtendedFNode:
        if op.is_symbol() and op.get_type() == REAL:
            i = FreshSymbol(INT, f"{op.symbol_name()}_int%s")
            r = FreshSymbol(REAL, f"{op.symbol_name()}_real%s")
            new_reals.append(r)
            return Plus(ToReal(i), r) #type: ignore
        else:
            return op

    return map_arithmetic_atom(f, atom_rewriter), new_reals


def flatten_plus(expr: ExtendedFNode) -> List[ExtendedFNode]:
    """Return a flat list of terms in a + b + c ... (non-recursive for other nodes)."""
    if expr.is_plus():
        out = []
        for a in expr.args():
            out.extend(flatten_plus(a))
        return out
    return [expr]

def split_by_type(terms: List[ExtendedFNode]) -> Tuple[List[ExtendedFNode], List[ExtendedFNode], ExtendedFNode]:
    """Split symbol terms into (int_syms, real_syms, const_sum).
       Assumes constants present only as Int/Real constants (or none).
    """

    ints: List[ExtendedFNode] = []
    reals: List[ExtendedFNode] = []
    const_sum: Optional[ExtendedFNode] = None

    for t in terms:
        if t.is_toreal():
            inner = cast(ExtendedFNode, t.args()[0])
            if inner.is_symbol() and inner.symbol_type() == INT:
                ints.append(inner)
            else:
                raise ValueError("ToReal wraps non-integer symbol")
        elif t.is_symbol():
            if t.symbol_type() == INT:
                ints.append(t)
            elif t.symbol_type() == REAL:
                reals.append(t)
            else:
                raise ValueError("unexpected symbol type")
        elif t.is_constant():
            const_sum = t if const_sum is None else cast(ExtendedFNode, Plus(const_sum, t))
        else:
            raise ValueError("unexpected term type: %s" % t.node_type())

    if const_sum is None:
        const_sum = cast(ExtendedFNode, Int(0)) if len(ints) > 0 else cast(ExtendedFNode, Real(0))

    assert const_sum is not None
    return ints, reals, const_sum

def decompose(f):
    def unwrap_toreal(term):
        """Unwrap ToReal(x) to just x, treating it as an integer."""
        if term.is_function_application() and term.is_toint():
            return term.args()[0]
        return term
    
    def analyze_sum_terms(expr):
        """Analyze a sum, unwrapping ToReal terms."""
        if not expr.is_plus():
            return None
        
        terms = flatten_plus(expr)
        unwrapped_terms = [unwrap_toreal(term) for term in terms]
        
        try:
            ints, reals, consts = split_by_type(unwrapped_terms)
            return ints, reals, consts
        except ValueError:
            return None

    def rewrite_atom(atom: ExtendedFNode) -> ExtendedFNode:
        if not (atom.is_equals() or atom.is_lt() or atom.is_le()):
            raise ValueError("unsupported atom shape")

        lhs, rhs = atom.args()
        
        # Pattern: (int + real) = k
        def match_int_real_eq_const(a, b) -> Optional[ExtendedFNode]:
            if not b.is_constant():
                return None
            
            terms_analysis = analyze_sum_terms(a)
            if not terms_analysis:
                return None
            
            ints, reals, _ = terms_analysis
            if len(ints) != 1 or len(reals) != 1:
                return None
                
            xi, xr = ints[0], reals[0]
            k = b.constant_value()
            
            if k == 0:
                return cast(ExtendedFNode, And(Equals(xi, Int(0)), Equals(xr, Real(0))))
            elif k == 1:
                return cast(ExtendedFNode, And(Equals(xi, Int(1)), Equals(xr, Real(0))))
            return None

        # Pattern: (int + real) < 0  
        def match_int_real_lt_zero(a, b) -> Optional[ExtendedFNode]:
            if not (b.is_constant() and b.constant_value() == 0):
                return None
            
            terms_analysis = analyze_sum_terms(a)
            if not terms_analysis:
                return None
                
            ints, reals, _ = terms_analysis
            if len(ints) != 1 or len(reals) != 1:
                return None
            return cast(ExtendedFNode, LT(ints[0], Int(0)))

        # Pattern: (xi + xr) + (yi + yr) = zi + zr
        # Where yr could implicitly be zero
        def match_double_sum_eq(a, b):
            a_analysis = analyze_sum_terms(a)
            b_analysis = analyze_sum_terms(b)

            if not a_analysis or not b_analysis:
                return None

            a_ints, a_reals, _ = a_analysis
            b_ints, b_reals, _ = b_analysis

            # We can only handle cases with 2 integer vars on LHS and 1 on RHS.
            if len(a_ints) != 2 or len(b_ints) != 1 or len(b_reals) != 1:
                return None

            xi, yi = a_ints
            zi = b_ints[0]
            zr = b_reals[0]

            # Case 1: xi + xr + yi + yr = zi + zr
            # The sum of two fractional parts can exceed 1, so we need carry logic.
            if len(a_reals) == 2:
                xr, yr = a_reals
                R = Plus(xr, yr)
                case1 = Implies(LT(R, Real(1)),
                               And(Equals(Plus(xi, yi), zi), Equals(R, zr)))
                case2 = Implies(GE(R, Real(1)),
                               And(Equals(Plus(Plus(xi, yi), Int(1)), zi),
                                   Equals(Minus(R, Real(1)), zr)))
                return And(case1, case2)

            # Case 2: xi + xr + yi = zi + zr (yr is implicitly zero)
            # The single fractional part xr cannot exceed 1, so no carry is possible.
            elif len(a_reals) == 1:
                xr = a_reals[0]
                # The rewrite simplifies to a direct split of the integer and real parts.
                return And(Equals(Plus(xi, yi), zi),
                           Equals(xr, zr))

            # If the number of reals on the LHS is not 1 or 2, we can't match.
            return None

        # Pattern: xi + xr = floor(yi + yr) - now handles ToReal transparently
        def match_floor_eq(a, b):
            if not (b.is_function_application() and b.is_toint()):
                return None
                
            a_analysis = analyze_sum_terms(a)
            if not a_analysis:
                return None
                
            a_ints, a_reals, _ = a_analysis
            if len(a_ints) != 1 or len(a_reals) != 1:
                return None
            
            floor_arg = b.args()[0]
            b_analysis = analyze_sum_terms(floor_arg)
            if not b_analysis:
                return None
                
            b_ints, _, _ = b_analysis
            if len(b_ints) != 1:
                return None
                
            xi, xr = a_ints[0], a_reals[0]
            yi = b_ints[0]
            return And(Equals(xr, Real(0)), Equals(xi, yi))

        # Pattern: (real + ToReal(int)) = real_constant
        def match_real_toreal_eq_const(a, b):
            if not (a.is_plus() and b.is_constant()):
                return None
            terms = flatten_plus(a)
            if len(terms) != 2:
                return None
            
            # Look for one real variable and one ToReal(int)
            real_var = None
            int_in_toreal = None
            
            for term in terms:
                if term.is_function_application() and term.is_toint():
                    int_in_toreal = term.args()[0]
                elif not term.is_constant():  # assume it's a real variable
                    real_var = term
            
            if real_var is None or int_in_toreal is None:
                return None
            
            # (real + ToReal(int)) = 0 -> real = 0 and int = 0
            if b.constant_value() == 0:
                return And(Equals(real_var, Real(0)), Equals(int_in_toreal, Int(0)))
            
            return None

        # Try all patterns
        if atom.is_equals():
            for matcher in [match_int_real_eq_const, match_double_sum_eq, match_floor_eq]:
                result = matcher(lhs, rhs) or matcher(rhs, lhs)
                if result:
                    return result
        
        if atom.is_lt():
            result = match_int_real_lt_zero(lhs, rhs) or match_int_real_lt_zero(rhs, lhs)
            if result:
                return result

        if len({v.get_type() for v in atom.get_free_variables()}) > 1:
            raise ValueError(f"Atom {atom.serialize()} did not match any supported pattern")
        else:
            return atom
    
    return map_atoms(f, rewrite_atom)

def compute_seperation(f):
    f_new = f

    # Only f_new should appear here
    f_new = clean_floors(f_new)
    f_new = make_input_format(f_new)
    f_new, new_reals = split_int_real(f_new)
    f_new = decompose(f_new)

    return And(f_new, *[And(LE(Real(0), r), LT(r, Real(1))) for r in new_reals])


if __name__ == "__main__":

    def _validate_separation(f):
        def validate_atom(atom):
            assert len({v.get_type() for v in atom.get_free_variables()}) <= 1
            return atom
    
        map_atoms(f, validate_atom)
        return True


    x = Symbol("x", REAL)
    y = Symbol("y", REAL)

    # 2. Define the input formula
    # f = 2*x + (-0.5)*y <= 3
    two_x = Times(Real(2), x)
    half_y = Times(Real(-0.5), y)
    lhs = Plus(two_x, half_y)
    rhs = Real(3)
    
    original_formula = LT(lhs, rhs)
    
    # 3. Run the complete decomposition process
    # This is the main function from your script
    decomposed_formula = compute_seperation(original_formula)
    print(decomposed_formula.serialize())
    _validate_separation(decomposed_formula)
