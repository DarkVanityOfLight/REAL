from itertools import chain
from typing import List, Mapping, Optional, Set, Tuple, cast
from pysmt.shortcuts import (GE, LE, LT, And, Equals, Exists, FreshSymbol, 
                            Implies, Int, Minus, Not, Or, Plus, Real, ToReal, substitute)
from pysmt.typing import BOOL, INT, REAL, PySMTType, _IntType, _RealType
import pysmt.operators as operators

from ramsey_elimination.existential_elimination import eliminate_existential_quantifier
from ramsey_elimination.integer_elimination import full_ramsey_elimination_int
from ramsey_elimination.real_elimination import full_ramsey_elimination_real
from ramsey_elimination.simplifications import arithmetic_solver, make_real_input_format
from ramsey_extensions.fnode import ExtendedFNode
from ramsey_extensions.shortcuts import Ramsey, ToInt
from ramsey_elimination.formula_utils import (fresh_bool_vector, generic_recursor, 
                                            map_arithmetic_atom, map_atoms, 
                                            ast_to_terms, collect_atoms)

from math import lcm, gcd
from fractions import Fraction


def create_typed_symbol(value: int, symbol_type: PySMTType, name_prefix: str) -> Tuple[ExtendedFNode, ExtendedFNode]:
    """Create a symbol of given type with a constraint that it equals the given value."""
    symbol = FreshSymbol(symbol_type, f"{name_prefix}_{symbol_type}_%s")
    
    constraint: ExtendedFNode
    match symbol_type:
        case _IntType(): constraint = Equals(symbol, Int(value)) #type: ignore
        case _RealType(): constraint = Equals(symbol, Real(value)) #type: ignore
        case _: raise ValueError(f"Unsupported type: {symbol_type.name}")
    
    return constraint, symbol #type: ignore


def create_zero(symbol_type: PySMTType) -> Tuple[ExtendedFNode, ExtendedFNode]:
    """Create a zero symbol of the given type."""
    return create_typed_symbol(0, symbol_type, "zero")


def create_one(symbol_type: PySMTType) -> Tuple[ExtendedFNode, ExtendedFNode]:
    """Create a one symbol of the given type."""
    return create_typed_symbol(1, symbol_type, "one")


def create_addition_constraint(x: ExtendedFNode, y: ExtendedFNode, z: ExtendedFNode) -> ExtendedFNode:
    """Create constraint: x + y = z"""
    return Equals(Plus(x, y), z) #type: ignore


def create_floor_constraint(x: ExtendedFNode, y: ExtendedFNode) -> ExtendedFNode:
    """Create constraint: x = floor(y)"""
    return Equals(x, ToInt(y)) #type: ignore


def build_powers_by_doubling(base: ExtendedFNode, count: int, symbol_type: PySMTType) -> Tuple[List[ExtendedFNode], List[ExtendedFNode]]:
    """
    Build sequence [base, 2*base, 4*base, 8*base, ...] up to count elements.
    Returns (power_symbols, construction_constraints).
    """
    if count <= 0:
        return [], []
    
    powers = [base]
    constraints = []
    
    for i in range(1, count):
        power_symbol: ExtendedFNode = FreshSymbol(symbol_type, f"power_2_{i}_%s") #type: ignore
        # power_symbol = powers[i-1] + powers[i-1] = 2 * powers[i-1]
        constraint = create_addition_constraint(powers[i-1], powers[i-1], power_symbol)
        
        powers.append(power_symbol)
        constraints.append(constraint)
    
    return powers, constraints


def sum_selected_terms(bit_pattern: str, terms: List[ExtendedFNode], 
                      zero_symbol: ExtendedFNode, symbol_type: PySMTType) -> Tuple[ExtendedFNode, List[ExtendedFNode]]:
    """
    Sum terms selected by bit_pattern (LSB-first), starting from zero_symbol.
    Returns (result_symbol, construction_constraints).
    """
    if not any(bit == "1" for bit in bit_pattern):
        return zero_symbol, []
    
    current_sum : ExtendedFNode = zero_symbol
    constraints = []
    
    for i, bit in enumerate(bit_pattern):
        if bit == "1" and i < len(terms):
            next_sum: ExtendedFNode = FreshSymbol(symbol_type, f"partial_sum_{i}_%s") #type: ignore
            constraint = create_addition_constraint(current_sum, terms[i], next_sum)
            constraints.append(constraint)
            current_sum = next_sum
    
    return current_sum, constraints


def build_integer_constant(n: int, symbol_type: PySMTType) -> Tuple[ExtendedFNode, List[ExtendedFNode]]:
    """
    Build constraints to represent integer n using only primitives:
    x = 0, x = 1, x + y = z
    """
    if n == 0:
        zero_constraint, zero_symbol = create_zero(symbol_type)
        return zero_symbol, [zero_constraint]
    
    constraints = []
    
    # Create basic symbols
    zero_constraint, zero_symbol = create_zero(symbol_type)
    one_constraint, one_symbol = create_one(symbol_type)
    constraints.extend([zero_constraint, one_constraint])
    
    abs_n = abs(n)
    
    if abs_n == 1:
        positive_result = one_symbol
    else:
        # Binary decomposition (LSB first)
        binary_bits = bin(abs_n)[2:][::-1]
        
        # Build powers of 2: [1, 2, 4, 8, ...]
        powers, power_constraints = build_powers_by_doubling(one_symbol, len(binary_bits), symbol_type)
        constraints.extend(power_constraints)
        
        # Sum selected powers based on binary representation
        positive_result, sum_constraints = sum_selected_terms(binary_bits, powers, zero_symbol, symbol_type)
        constraints.extend(sum_constraints)
    
    if n > 0:
        return positive_result, constraints
    
    # Handle negative: create y such that y + positive_result = 0
    negative_symbol : ExtendedFNode = FreshSymbol(symbol_type, f"negative_{symbol_type}_%s") #type: ignore
    negative_constraint = create_addition_constraint(negative_symbol, positive_result, zero_symbol)
    constraints.append(negative_constraint)
    
    return negative_symbol, constraints


def build_constant_multiplication(coefficient: int, variable: ExtendedFNode, 
                                 symbol_type: PySMTType) -> Tuple[ExtendedFNode, List[ExtendedFNode]]:
    """
    Build constraints for coefficient * variable using doubling and addition.
    Returns (result_symbol, construction_constraints).
    """
    variable = variable if variable.is_symbol() else variable.arg(0)
    assert variable.is_symbol()
    constraints = []
    
    zero_constraint, zero_symbol = create_zero(symbol_type)
    constraints.append(zero_constraint)
    
    # Handle trivial cases
    if coefficient == 0:
        return zero_symbol, constraints
    
    if abs(coefficient) == 1:
        if coefficient > 0:
            return variable, constraints
        
        # coefficient = -1: create neg such that neg + variable = 0
        negative_symbol : ExtendedFNode = FreshSymbol(symbol_type, f"neg_{variable.symbol_name()}_%s") #type: ignore
        negative_constraint = create_addition_constraint(negative_symbol, variable, zero_symbol)
        constraints.append(negative_constraint)
        return negative_symbol, constraints
    
    # General case: binary decomposition
    abs_coeff = abs(coefficient)
    binary_bits = bin(abs_coeff)[2:][::-1]  # LSB first
    
    # Build multiples: [variable, 2*variable, 4*variable, ...]
    multiples, multiple_constraints = build_powers_by_doubling(variable, len(binary_bits), symbol_type)
    constraints.extend(multiple_constraints)
    
    # Sum selected multiples
    positive_result, sum_constraints = sum_selected_terms(binary_bits, multiples, zero_symbol, symbol_type)
    constraints.extend(sum_constraints)
    
    if coefficient > 0:
        return positive_result, constraints
    
    # Handle negative coefficient
    negative_symbol: ExtendedFNode = FreshSymbol(symbol_type, f"neg_{positive_result.symbol_name()}_%s") #type: ignore
    negative_constraint = create_addition_constraint(negative_symbol, positive_result, zero_symbol)
    constraints.append(negative_constraint)
    
    return negative_symbol, constraints


def clean_floor_expressions(formula: ExtendedFNode) -> ExtendedFNode:
    """Replace ToInt expressions with fresh variables and appropriate constraints."""
    extra_constraints = []
    
    def floor_cleaner(node: ExtendedFNode) -> ExtendedFNode:
        if node.is_toint():
            # Create fresh variables for floor operation
            inner_real : ExtendedFNode = FreshSymbol(REAL, f"floor_input_%s") #type: ignore
            outer_int : ExtendedFNode = FreshSymbol(INT, f"floor_output_%s") #type: ignore
            
            # Add constraints
            inner_constraint = Equals(inner_real, node.arg(0))
            floor_constraint = create_floor_constraint(outer_int, inner_real)
            
            extra_constraints.extend([inner_constraint, floor_constraint])
            return outer_int
        
        return node
    
    cleaned_formula = generic_recursor(formula, floor_cleaner)
    return And(cleaned_formula, *extra_constraints) if extra_constraints else cleaned_formula #type: ignore


def normalize_arithmetic_atom(atom: ExtendedFNode) -> Tuple[ExtendedFNode, List[ExtendedFNode]]:
    """
    Transform arithmetic atom into canonical form using only basic primitives.
    Returns (canonical_atom, construction_constraints).
    """
    left, right = atom.arg(0), atom.arg(1)
    
    # Skip atoms that already contain floor operations
    if left.is_toint() or right.is_toint():
        return atom, []
    
    # Extract coefficients and constants from both sides
    left_coeffs, left_const = ast_to_terms(left)
    right_coeffs, right_const = ast_to_terms(right)
    
    # Normalize to: sum(coeffs * vars) ~ constant
    coeffs, _, constant = arithmetic_solver(left_coeffs, left_const, right_coeffs, right_const, set())
    
    def F(x): 
        return Fraction(x).limit_denominator() if isinstance(x, float) else Fraction(x)

    fracs = {v: F(c) for v, c in coeffs.items()}
    c = F(constant)

    # scale to integers
    denoms = [f.denominator for f in fracs.values()] + [c.denominator]
    scale = lcm(*denoms) if denoms else 1
    scaled_terms = [(v, (f * scale).numerator) for v, f in fracs.items()]
    scaled_const = (c * scale).numerator

    # reduce by gcd
    nonzero = [abs(n) for _, n in scaled_terms] + ([abs(scaled_const)] if scaled_const != 0 else [])
    g = gcd(*nonzero) if nonzero else 1
    if g > 1:
        scaled_terms = [(v, n // g) for v, n in scaled_terms]
        scaled_const //= g
    
    constraints = []
    
    # Build left-hand side from scaled terms
    if not scaled_terms:
        lhs_constraint, lhs_symbol = create_zero(INT)
        constraints.append(lhs_constraint)
        result_type = INT
    else:
        # Determine result type based on variable types
        has_real = any(var.symbol_type() == REAL for var, _ in scaled_terms)
        result_type = REAL if has_real else INT
        
        # Build each term
        term_symbols = []
        for var, coeff in scaled_terms:
            term_symbol, term_constraints = build_constant_multiplication(coeff, var, var.symbol_type())
            constraints.extend(term_constraints)
            
            # Convert to real if needed
            if var.symbol_type() == INT and result_type == REAL:
                term_symbol = ToReal(term_symbol)
            
            term_symbols.append(term_symbol)
        
        # Sum all terms
        lhs_symbol: ExtendedFNode = term_symbols[0]
        for i in range(1, len(term_symbols)):
            sum_symbol: ExtendedFNode = FreshSymbol(result_type, f"lhs_sum_{i}_%s") #type: ignore
            sum_constraint = create_addition_constraint(lhs_symbol, term_symbols[i], sum_symbol)
            constraints.append(sum_constraint)
            lhs_symbol = sum_symbol
    
    # Build right-hand side constant
    rhs_symbol: ExtendedFNode
    rhs_symbol, rhs_constraints = build_integer_constant(scaled_const, result_type)
    constraints.extend(rhs_constraints)
    
    # Create difference: lhs - rhs
    neg_rhs, neg_constraints = build_constant_multiplication(-1, rhs_symbol, result_type)
    constraints.extend(neg_constraints)
    
    diff_symbol: ExtendedFNode = FreshSymbol(result_type, "difference_%s") #type: ignore
    diff_constraint = create_addition_constraint(lhs_symbol, neg_rhs, diff_symbol)
    constraints.append(diff_constraint)
    
    # Create canonical constants
    zero_constraint, zero_symbol = create_zero(result_type)
    constraints.append(zero_constraint)
    
    # Build canonical atom based on original relation
    canonical_atom: ExtendedFNode
    match atom.node_type():
        case operators.EQUALS: canonical_atom = create_addition_constraint(diff_symbol, zero_symbol, zero_symbol)
        case operators.LT: canonical_atom = LT(diff_symbol, Int(0) if result_type == INT else Real(0)) #type: ignore
        case _: raise ValueError(f"Unsupported relation: {atom.node_type()}")
    
    return canonical_atom, constraints


def transform_to_input_format(formula: ExtendedFNode) -> ExtendedFNode:
    """Transform formula to use only basic arithmetic primitives."""
    additional_constraints = []
    
    def atom_transformer(atom: ExtendedFNode) -> ExtendedFNode:
        normalized_atom, constraints = normalize_arithmetic_atom(atom)
        additional_constraints.extend(constraints)
        return normalized_atom
    
    transformed_formula = map_atoms(formula, atom_transformer)
    
    if additional_constraints:
        return And(transformed_formula, *additional_constraints) #type: ignore
    return transformed_formula


def separate_integer_real_types(formula: ExtendedFNode, 
                               tracked_vars: Set[ExtendedFNode]) -> Tuple[ExtendedFNode, List[ExtendedFNode], Mapping]:
    """
    Split real variables into integer + fractional parts.
    Returns (transformed_formula, real_fractional_vars, variable_mapping).
    """
    fractional_vars = []
    tracking_map = {}
    
    def variable_splitter(node: ExtendedFNode) -> ExtendedFNode:
        if node.is_symbol() and node.get_type() == REAL:
            integer_part = FreshSymbol(INT, f"{node.symbol_name()}_int_%s")
            fractional_part = FreshSymbol(REAL, f"{node.symbol_name()}_frac_%s")
            
            if node in tracked_vars:
                tracking_map[node] = (integer_part, fractional_part)
            
            fractional_vars.append(fractional_part)
            return Plus(ToReal(integer_part), fractional_part) #type: ignore
        
        return node
    
    transformed = map_arithmetic_atom(formula, variable_splitter)
    return transformed, fractional_vars, tracking_map


def flatten_addition(expr: ExtendedFNode) -> List[ExtendedFNode]:
    """Flatten nested additions into a list of terms."""
    if expr.is_plus():
        terms = []
        for arg in expr.args():
            terms.extend(flatten_addition(arg))
        return terms
    return [expr]


def categorize_terms_by_type(terms: List[ExtendedFNode]) -> Tuple[List[ExtendedFNode], List[ExtendedFNode], ExtendedFNode]:
    """
    Categorize terms into integer symbols, real symbols, and constants.
    Returns (integer_terms, real_terms, constant_sum).
    """
    integer_terms: List[ExtendedFNode] = []
    real_terms: List[ExtendedFNode] = []
    constant_sum: Optional[ExtendedFNode] = None
    
    for term in terms:
        if term.is_toreal() and term.args()[0].is_symbol():
            # ToReal(integer_symbol)
            inner_symbol = term.args()[0]
            if inner_symbol.symbol_type() == INT:
                integer_terms.append(inner_symbol)
            else:
                raise ValueError("ToReal wraps non-integer symbol")
        
        elif term.is_symbol():
            if term.symbol_type() == INT:
                integer_terms.append(term)
            elif term.symbol_type() == REAL:
                real_terms.append(term)
            else:
                raise ValueError(f"Unexpected symbol type: {term.symbol_type()}")
        
        elif term.is_constant():
            if constant_sum is None:
                constant_sum = term
            else:
                constant_sum = Plus(constant_sum, term) #type: ignore
        
        else:
            raise ValueError(f"Unexpected term type: {term.node_type()}")
    
    # Default constant if none found
    if constant_sum is None:
        constant_sum = Int(0) if integer_terms else Real(0) #type: ignore
    
    assert constant_sum
    return integer_terms, real_terms, constant_sum


# ============================================================================
# Formula Decomposition with Pattern Matching
# ============================================================================

def decompose_mixed_arithmetic(formula: ExtendedFNode) -> ExtendedFNode:
    """
    Decompose mixed integer/real arithmetic into simpler patterns.
    Handles floor operations and mixed-type equations.
    """
    
    def analyze_addition_terms(expr: ExtendedFNode) -> Optional[Tuple]:
        """Analyze sum expression, unwrapping ToReal where appropriate."""
        if not expr.is_plus():
            return None
        
        terms = flatten_addition(expr)
        # Unwrap ToReal from ToInt expressions (floor operations)
        unwrapped_terms = [
            term.args()[0] if term.is_toint() else term 
            for term in terms
        ]
        
        try:
            return categorize_terms_by_type(unwrapped_terms)
        except ValueError:
            return None
    
    def rewrite_arithmetic_atom(atom: ExtendedFNode) -> ExtendedFNode:
        """Rewrite atoms using pattern matching for common mixed-type expressions."""
        if not (atom.is_equals() or atom.is_lt() or atom.is_le()):
            raise ValueError(f"Unsupported atom type: {atom.node_type()}")
        
        lhs, rhs = atom.args()
        
        # Pattern: integer + real = constant
        def match_int_real_equals_constant(left, right):
            if not right.is_constant():
                return None
            
            analysis = analyze_addition_terms(left)
            if not analysis:
                return None
            
            ints, reals, _ = analysis
            if len(ints) != 1 or len(reals) != 1:
                return None
            
            int_var, real_var = ints[0], reals[0]
            constant_value = right.constant_value()
            
            # Handle specific constant values
            if constant_value == 0:
                return And(Equals(int_var, Int(0)), Equals(real_var, Real(0)))
            elif constant_value == 1:
                return And(Equals(int_var, Int(1)), Equals(real_var, Real(0)))
            
            return None
        
        # Pattern: integer + real < 0
        def match_int_real_less_than_zero(left, right) -> Optional[ExtendedFNode]:
            if not (right.is_constant() and right.constant_value() == 0):
                return None
            
            analysis = analyze_addition_terms(left)
            if not analysis:
                return None
            
            ints, reals, _ = analysis
            if len(ints) != 1 or len(reals) != 1:
                return None
            
            return LT(ints[0], Int(0)) #type: ignore
        
        # Pattern: sum equations with carry logic
        def match_sum_with_carry(left, right) -> Optional[ExtendedFNode]:
            left_analysis = analyze_addition_terms(left)
            right_analysis = analyze_addition_terms(right)
            
            if not (left_analysis and right_analysis):
                return None
            
            left_ints, left_reals, _ = left_analysis
            right_ints, right_reals, _ = right_analysis
            
            # Must have specific structure for carry logic
            if len(left_ints) != 2 or len(right_ints) != 1 or len(right_reals) != 1:
                return None
            
            xi, yi = left_ints
            zi, zr = right_ints[0], right_reals[0]
            
            if len(left_reals) == 2:
                # Two fractional parts: carry possible
                xr, yr = left_reals
                fractional_sum = Plus(xr, yr)
                
                no_carry = Implies(
                    LT(fractional_sum, Real(1)),
                    And(Equals(Plus(xi, yi), zi), Equals(fractional_sum, zr))
                )
                
                with_carry = Implies(
                    GE(fractional_sum, Real(1)),
                    And(
                        Equals(Plus(Plus(xi, yi), Int(1)), zi),
                        Equals(Minus(fractional_sum, Real(1)), zr)
                    )
                )
                
                return And(no_carry, with_carry) #type: ignore
            
            elif len(left_reals) == 1:
                # One fractional part: no carry possible
                xr = left_reals[0]
                return And(Equals(Plus(xi, yi), zi), Equals(xr, zr)) #type: ignore
            
            return None
        
        # Pattern: floor operations
        def match_floor_operation(left, right):
            # Try to match floor on the right side
            if not right.is_toint():
                return None
            
            floor_arg = right.args()[0]
            floor_analysis = analyze_addition_terms(floor_arg)
            
            if not floor_analysis:
                return None
            
            floor_ints, floor_reals, _ = floor_analysis
            if len(floor_ints) != 1 or len(floor_reals) != 1:
                return None
            
            floor_int_part = floor_ints[0]
            
            # Check left side structure
            left_analysis = analyze_addition_terms(left)
            
            if left_analysis:
                left_ints, left_reals, _ = left_analysis
                if len(left_ints) == 1 and len(left_reals) == 1:
                    # Pattern: xi + xr = floor(yi + yr)
                    xi, xr = left_ints[0], left_reals[0]
                    return And(Equals(xr, Real(0)), Equals(xi, floor_int_part))
            
            # Pattern: xi = floor(yi + yr)
            if left.get_type() == INT and not left.is_plus():
                return Equals(left, floor_int_part)
            
            return None
        
        # Apply pattern matching
        if atom.is_equals():
            for pattern_matcher in [match_int_real_equals_constant, match_sum_with_carry, match_floor_operation]:
                result = pattern_matcher(lhs, rhs) or pattern_matcher(rhs, lhs)
                if result:
                    return result
        
        if atom.is_lt():
            result = match_int_real_less_than_zero(lhs, rhs)
            if result:
                return result
        
        # Fallback: ensure single type
        free_vars = atom.get_free_variables()
        if len({var.get_type() for var in free_vars}) > 1:
            raise ValueError(f"Atom contains mixed types and no pattern matched: {atom.serialize()}")
        
        return atom
    
    return map_atoms(formula, rewrite_arithmetic_atom)


# ============================================================================
# Main Processing Pipeline
# ============================================================================

def compute_type_separation(formula: ExtendedFNode, 
                           free_variables: Set[ExtendedFNode]) -> Tuple[ExtendedFNode, Mapping]:
    """
    Main pipeline to separate mixed integer/real arithmetic.
    Returns (separated_formula, free_variable_mapping).
    """
    # Step 1: Clean floor expressions
    cleaned = clean_floor_expressions(formula)
    
    # Step 2: Transform to input format (basic primitives only)
    normalized = transform_to_input_format(cleaned)
    
    # Step 3: Split real variables into integer + fractional parts
    with_splits, fractional_vars, var_mapping = separate_integer_real_types(normalized, free_variables)
    
    # Step 4: Decompose mixed arithmetic patterns
    decomposed = decompose_mixed_arithmetic(with_splits)
    
    # Step 5: Add fractional part constraints (0 <= frac < 1)
    fractional_constraints = [
        And(LE(Real(0), frac_var), LT(frac_var, Real(1))) 
        for frac_var in fractional_vars
    ]
    
    final_formula: ExtendedFNode = And(decomposed, *fractional_constraints) if fractional_constraints else decomposed #type: ignore
    
    return final_formula, var_mapping


# ============================================================================
# Ramsey Elimination for Mixed Types
# ============================================================================

def eliminate_ramsey_mixed(quantified_formula: ExtendedFNode) -> ExtendedFNode:
    """Eliminate Ramsey quantifiers from mixed integer/real formulas."""
    
    # Extract the main formula from quantifier structure
    inner_formula = quantified_formula.arg(0)
    
    # Collect atoms by type
    equalities, _, inequalities = collect_atoms(inner_formula)
    all_atoms = equalities + inequalities
    
    real_atoms = [atom for atom in all_atoms if atom.arg(0).get_type() == REAL]
    int_atoms = [atom for atom in all_atoms if atom.arg(0).get_type() == INT]
    
    # Create propositional variables for atoms
    int_props = fresh_bool_vector("p_{}_%s", len(int_atoms))
    real_props = fresh_bool_vector("q_{}_%s", len(real_atoms))
    
    # Create substitution maps
    int_substitution = {atom: prop for atom, prop in zip(int_atoms, int_props)}
    real_substitution = {atom: prop for atom, prop in zip(real_atoms, real_props)}
    
    # Build propositional skeleton
    prop_skeleton = inner_formula.substitute(int_substitution | real_substitution)
    
    # Create implication constraints
    int_implications = And([Implies(prop, atom) for prop, atom in zip(int_props, int_atoms)])
    real_implications = And([Implies(prop, atom) for prop, atom in zip(real_props, real_atoms)])
    
    # Extract quantifier information
    left: Tuple[ExtendedFNode]
    right: Tuple[ExtendedFNode]
    left, right = quantified_formula.quantifier_vars() #type: ignore
    int_vars = tuple(zip(*[(l, r) for l, r in zip(left, right) if l.symbol_type() == INT])) or ((), ())
    real_vars = tuple(zip(*[(l, r) for l, r in zip(left, right) if l.symbol_type() == REAL])) or ((), ())
    
    # Apply Ramsey elimination to each type
    int_ramsey = Ramsey(int_vars[0], int_vars[1], int_implications)
    real_ramsey = Ramsey(real_vars[0], real_vars[1], real_implications)
    
    eliminated_int = full_ramsey_elimination_int(int_ramsey)
    eliminated_real = full_ramsey_elimination_real(real_ramsey)
    
    # Create decision variable
    decision_var = FreshSymbol(BOOL, "ramsey_decision%s")
    
    # Build substituted implications
    int_var_map = {y: x for x, y in zip(int_vars[0], int_vars[1])}
    real_var_map = {y: x for x, y in zip(real_vars[0], real_vars[1])}
    
    substituted_int_implications = substitute(int_implications, int_var_map)
    substituted_real_implications = substitute(real_implications, real_var_map)
    
    # Build final formula parts
    real_part = Or(
        eliminated_real,
        And(Not(decision_var), Exists(real_vars[0], substituted_real_implications))
    )
    
    int_part = Or(
        eliminated_int,
        And(decision_var, Exists(int_vars[0], substituted_int_implications))
    )
    
    # Combine all variables for final existential quantification
    all_existential_vars = int_props + real_props + [decision_var]
    
    return Exists(all_existential_vars, And(prop_skeleton, real_part, int_part)) #type: ignore


def restore_original_variables(formula: ExtendedFNode, 
                              variable_mapping: Mapping[ExtendedFNode, Tuple[ExtendedFNode, ExtendedFNode]]) -> ExtendedFNode:
    """Restore original variables from their integer/fractional decomposition."""
    
    substitution_map = {}
    
    for original_var, (int_part, frac_part) in variable_mapping.items():
        if original_var.symbol_type() == INT:
            # Integer variables: just use integer part
            substitution_map[int_part] = original_var
        else:
            # Real variables: int_part -> floor(original), frac_part -> original - floor(original)
            substitution_map[int_part] = ToInt(original_var)
            substitution_map[frac_part] = Minus(original_var, ToReal(ToInt(original_var)))
    
    return formula.substitute(substitution_map)


def requantify(formula: ExtendedFNode,
               ramsey: Tuple[Tuple[ExtendedFNode, ...], Tuple[ExtendedFNode, ...]],
               ex_vars: List[ExtendedFNode],
               free_vars: List[ExtendedFNode]):
    """Re-quantify all free variables in `formula` that are not in `free_vars`,
    the explicit existentials, or the two Ramsey tuples."""

    excluded: Set[ExtendedFNode] = set(free_vars) \
        | set(ex_vars) \
        | set(chain(ramsey[0], ramsey[1]))

    to_requantify = [v for v in formula.get_free_variables() if v not in excluded]

    return Ramsey(*ramsey, Exists(ex_vars + to_requantify, formula))


def full_mixed_ramsey_elimination(quantified_formula: ExtendedFNode) -> ExtendedFNode:
    """
    Complete pipeline for eliminating Ramsey quantifiers from mixed integer/real formulas.
    """
    # Extract free variables and parse nested quantifier structure
    free_vars = quantified_formula.get_free_variables()
    formula = quantified_formula.arg(0)

    ramsey_vars = cast(Tuple[Tuple[ExtendedFNode, ...], Tuple[ExtendedFNode, ...]], 
                       quantified_formula.quantifier_vars())
    
    # Navigate through nested existential quantifiers to get core formula
    inner = quantified_formula.arg(0)
    ex_vars = []
    if inner.is_exists():
        ex_vars = inner.quantifier_vars()
        formula = inner.arg(0)
    
    
    # Step 1: Convert <= to (< OR =) for easier processing
    def convert_le_to_lt_or_eq(atom: ExtendedFNode) -> ExtendedFNode:
        if atom.is_le():
            left, right = atom.arg(0), atom.arg(1)
            return Or(LT(left, right), Equals(left, right)) #type: ignore
        return atom
    
    no_le_formula = map_atoms(formula, convert_le_to_lt_or_eq)
    
    # Step 2: Normalize (push negations inward)
    normalized = make_real_input_format(no_le_formula)
    
    # Step 3: Separate integer and real types
    separated, var_mapping = compute_type_separation(normalized, free_vars)
    
    # Step 4: Restore original variables and re-quantify
    with_original_vars = restore_original_variables(separated, var_mapping)
    requantified = requantify(with_original_vars, ramsey_vars, ex_vars, free_vars)
    
    next = requantified
    # Step 5: Eliminate existential quantifiers
    if quantified_formula.arg(0).is_exists():
        next = eliminate_existential_quantifier(requantified)
        print(f"Existential eliminated: {next.size()}")
    
    # Step 6: Apply mixed Ramsey elimination
    return eliminate_ramsey_mixed(next)

def eliminate_mixed_ramsey_from_separated(quantified_formula: ExtendedFNode) -> ExtendedFNode:
    """
    Eliminates mixed existential and Ramsey quantifiers from a formula
    that is already type-separated.
    """
    next_formula = (eliminate_existential_quantifier(quantified_formula)
                    if quantified_formula.arg(0).is_exists() else quantified_formula)
    return eliminate_ramsey_mixed(next_formula)
