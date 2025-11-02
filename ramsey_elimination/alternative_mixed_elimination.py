

from typing import Tuple, cast

from pysmt.exceptions import PysmtTypeError
from pysmt.shortcuts import And, LE, LT, Equals, FreshSymbol, Int, Or, Plus, Real, ToReal

from ramsey_elimination.formula_utils import ast_to_terms, bool_vector, collect_atoms, fresh_bool_vector, reconstruct_from_coeff_map
from ramsey_elimination.real_elimination import eliminate_equality_atom_real
from ramsey_elimination.simplifications import SumOfTerms, arithmetic_solver, make_mixed_input_format
from ramsey_extensions.fnode import ExtendedFNode
import pysmt.typing as typ

from math import floor

def split_terms(terms: SumOfTerms) -> Tuple[SumOfTerms, SumOfTerms]:
    """
    Given a SumOfTerms mapping,
    return (SumOfTerms(integer only), SumOfTerms(real only))
    """
    ints = {}
    reals = {}
    for variable, coeff in terms.items():
        if variable.symbol_type() == typ.INT:
            ints[variable] = coeff
        elif variable.symbol_type() == typ.REAL:
            reals[variable] = coeff
        else:
            raise PysmtTypeError(f"Expeceted real or integer symbol got: {variable}")

    return ints, reals

# TODO: Handle modulo equalities
def decompose_equality(phi: ExtendedFNode):
    assert phi.is_equals()

    left, left_c = ast_to_terms(phi.arg(0))
    right, right_c = ast_to_terms(phi.arg(1))
    var_terms, _, C = arithmetic_solver(left, left_c, right, right_c, set())

    int_terms, real_terms = split_terms(var_terms)
    int_bridge = FreshSymbol(typ.INT, "c_i%s")
    real_bridge = FreshSymbol(typ.REAL, "c_r%s")

    C_i = floor(C)
    C_r = C - C_i
    real_part = Equals(reconstruct_from_coeff_map(real_terms, 0, Real),
                       Plus(real_bridge, C_r))
    int_part = Equals(
        Plus(reconstruct_from_coeff_map(int_terms, 0, Int), int_bridge),
        C_i
    )

    bridge = Equals(real_bridge, ToReal(int_bridge))

    return real_part, int_part, bridge, [real_bridge, int_bridge]

def decompose_inequality(phi: ExtendedFNode):
    assert phi.is_lt() or phi.is_le()

    left, left_c = ast_to_terms(phi.arg(0))
    right, right_c = ast_to_terms(phi.arg(1))
    var_terms, _, C = arithmetic_solver(left, left_c, right, right_c, set())

    int_terms, real_terms = split_terms(var_terms)
    int_bridge = FreshSymbol(typ.INT, "c_i%s")
    real_bridge = FreshSymbol(typ.REAL, "c_r%s")
    real_dummy = FreshSymbol(typ.REAL, "R_%s")

    C_i = floor(C)
    C_r = C - C_i

    real_part = Equals(reconstruct_from_coeff_map(real_terms, 0, Real),
                       Plus(real_dummy, real_bridge))

    dummy_restriction = And(LE(Real(0), real_dummy), LT(real_dummy, Real(1)))
    int_reconstructed = Plus(reconstruct_from_coeff_map(int_terms, 0, Int), int_bridge)
    
    in_eq_enforcing = Or(
        LT(int_reconstructed, C_i),
        And(Equals(int_reconstructed, C_i), LT(real_dummy, C_r))
    )
    bridge = Equals(real_bridge, ToReal(int_bridge))

    return real_part, dummy_restriction, in_eq_enforcing, bridge, [int_bridge, real_bridge, real_dummy]



def mixed_elimination_preparation(phi: ExtendedFNode):
    assert phi.is_ramsey()

    vars1, vars2 = phi.quantifier_vars()
    real_vars1, real_vars2 = [var for var in vars1 if var.symbol_type() == typ.REAL], [var for var in vars2 if var.symbol_type() == typ.REAL]
    int_vars1, int_vars2 = [var for var in vars1 if var.symbol_type() == typ.INT], [var for var in vars2 if var.symbol_type() == typ.INT]
    
    _ex = cast(ExtendedFNode, phi.arg(0))
    existential_vars = list(_ex.quantifier_vars()) if _ex.is_exists() else []
    phi_p = make_mixed_input_format(phi.arg(0))

    eqs, mod_eqs, ineqs = collect_atoms(phi)

    p = fresh_bool_vector("p_{}%s", len(eqs) + len(mod_eqs) + len(ineqs))
    p_mapping = {atom: p[i] for i, atom in enumerate(eqs + mod_eqs + ineqs) }
    skel = phi_p.substitute(p_mapping)
    sel_var = FreshSymbol(typ.INT, "s%s")

    real_atoms = []
    int_atoms = []
    bridge_atoms = []
    for eq in eqs:
        real_part, int_part, bridge, bridge_vars = decompose_equality(eq)
        real_atoms += real_part
    for ineq in ineqs:       
        real_part, dummy_restriction, in_eq_enforcing, bridge, ex_vars = decompose_inequality(ineq)


