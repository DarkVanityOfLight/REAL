from dataclasses import dataclass, field

from typing import Dict, List, Tuple, cast

from pysmt.exceptions import PysmtTypeError
from pysmt.shortcuts import And, LE, LT, Equals, Exists, FreshSymbol, Implies, Int, Not, Or, Plus, Real, Symbol, ToReal

from ramsey_elimination.formula_utils import ast_to_terms, bool_vector, collect_atoms, fresh_bool_vector, fresh_int_vector, fresh_real_vector, map_atoms, reconstruct_from_coeff_map
from ramsey_elimination.integer_elimination import eliminate_eq_atom_int, eliminate_inequality_atom_int
from ramsey_elimination.real_elimination import eliminate_equality_atom_real, eliminate_inequality_atom_real
from ramsey_elimination.simplifications import SumOfTerms, arithmetic_solver, make_mixed_input_format
from ramsey_extensions.fnode import ExtendedFNode
import pysmt.typing as typ

from math import floor


#TODO: ToInt operations

@dataclass
class EqualityDecomposition:
    pure_atoms: ExtendedFNode
    bridge_atom: ExtendedFNode
    int_bridge_var: ExtendedFNode = field(kw_only=True)
    real_bridge_var: ExtendedFNode = field(kw_only=True)

@dataclass
class StrictInequalityDecomposition:
    pure_atoms: ExtendedFNode
    bridge: ExtendedFNode
    int_bridge_var: ExtendedFNode = field(kw_only=True)
    real_bridge_var: ExtendedFNode = field(kw_only=True)
    real_dummy: ExtendedFNode = field(kw_only=True)


@dataclass
class BridgeElimination:
    v1a: Tuple[ExtendedFNode, ...]
    v2a: Tuple[ExtendedFNode, ...]
    v1a0: Tuple[ExtendedFNode, ...]
    v2a0: Tuple[ExtendedFNode, ...]

    v1d: Tuple[ExtendedFNode, ...]
    v2d: Tuple[ExtendedFNode, ...]
    v1dc: Tuple[ExtendedFNode, ...]
    v2dc: Tuple[ExtendedFNode, ...]
    v1dinf: Tuple[ExtendedFNode, ...]
    v2dinf: Tuple[ExtendedFNode, ...]



# s = 0 => real finite, int infinite
# s = 1 => int finite, real infinite
# s = 2 => int infinite, real infinite

# We collect one atom for each of these

@dataclass
class MixedEqualityEliminationResult:
    var: ExtendedFNode
    finite_real_clique: ExtendedFNode
    finite_int_clique: ExtendedFNode
    infinite_int_clique: ExtendedFNode
    infinite_real_clique: ExtendedFNode

    finite_real_bridge: ExtendedFNode
    finite_int_bridge: ExtendedFNode
    mixed_infinite_bridge: ExtendedFNode

@dataclass
class MixedInequalityEliminationResult:
    
    var: ExtendedFNode
    skeleton: ExtendedFNode
    skeleton_vars: Tuple[ExtendedFNode]

    int_admissibility: ExtendedFNode
    real_admissibility: ExtendedFNode

    # Assume these are of the form AND p_i -> a_i
    finite_real_clique: ExtendedFNode
    finite_int_clique: ExtendedFNode
    infinite_int_clique: ExtendedFNode
    infinite_real_clique: ExtendedFNode

    finite_real_bridge: ExtendedFNode
    finite_int_bridge: ExtendedFNode
    mixed_infinite_bridge: ExtendedFNode


type Decomposition = EqualityDecomposition | StrictInequalityDecomposition
type MixedEliminationResult = MixedEqualityEliminationResult | MixedInequalityEliminationResult

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

def decompose_equality(phi: ExtendedFNode) -> EqualityDecomposition:
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
    return EqualityDecomposition(And(real_part, int_part), bridge, int_bridge_var=int_bridge, real_bridge_var=real_bridge)

def decompose_inequality(phi: ExtendedFNode) -> StrictInequalityDecomposition:
    assert phi.is_lt() or phi.is_le()

    left, left_c = ast_to_terms(phi.arg(0))
    right, right_c = ast_to_terms(phi.arg(1))
    var_terms, _, C = arithmetic_solver(left, left_c, right, right_c, set())

    int_terms, real_terms = split_terms(var_terms)
    int_bridge: ExtendedFNode = FreshSymbol(typ.INT, "c_i%s")
    real_bridge: ExtendedFNode = FreshSymbol(typ.REAL, "c_r%s")
    real_dummy: ExtendedFNode = FreshSymbol(typ.REAL, "R_%s")

    C_i = floor(C)
    C_r = C - C_i

    real_part: ExtendedFNode = Equals(reconstruct_from_coeff_map(real_terms, 0, Real),
                       Plus(real_dummy, real_bridge))

    dummy_restriction: Tuple[ExtendedFNode, ExtendedFNode] = (LE(Real(0), real_dummy), LT(real_dummy, Real(1)))
    int_reconstructed: ExtendedFNode = Plus(reconstruct_from_coeff_map(int_terms, 0, Int), int_bridge)
    
    int_ineq = LT(int_reconstructed, C_i)
    real_ineq = And(Equals(int_reconstructed, C_i), LT(real_dummy, C_r))
    bridge: ExtendedFNode = Equals(real_bridge, ToReal(int_bridge))

    return StrictInequalityDecomposition(
        And(real_part, *dummy_restriction, Or(int_ineq, real_ineq),), bridge,
        int_bridge_var=int_bridge, real_bridge_var=real_bridge, real_dummy=real_dummy
    )


def eliminate_bridge_atom(*,v1_dc, v2_dc, v1_a, v1_dinf, w2_a, w2_dinf, v1_a0, w2_a0, v1_d0, w2_d0):
    dc_conditions = And(
        Equals(v1_dc, Real(0)), Equals(v2_dc, Real(0))
    )
    step_conditions = And(
        Equals(ToReal(v1_a), v1_dinf), Equals(ToReal(w2_a), w2_dinf)
    )
    start_conditions = And(
        Equals(ToReal(Plus(v1_a0, w2_a0)), Plus(v1_d0, w2_d0))
    )

    return And(dc_conditions, step_conditions, start_conditions)

def mixed_elimination(phi: ExtendedFNode):
    assert phi.is_ramsey()

    vars1, vars2 = phi.quantifier_vars()
    real_vars1, real_vars2 = [var for var in vars1 if var.symbol_type() == typ.REAL], [var for var in vars2 if var.symbol_type() == typ.REAL]
    int_vars1, int_vars2 = [var for var in vars1 if var.symbol_type() == typ.INT], [var for var in vars2 if var.symbol_type() == typ.INT]

    orig_real_len = len(real_vars1)
    orig_int_len = len(int_vars1)


    phi_p = make_mixed_input_format(phi.arg(0))

    eqs, _, ineqs = collect_atoms(phi_p)

    pure_atoms: List[ExtendedFNode] = []
    # atom |-> decomposition
    decomposition_mapping: Dict[ExtendedFNode, Decomposition] = {}
    num_impure = 0
    num_impure_ineqs = 0
    for eq in eqs:
        if len({v.get_type() for v in eq.get_free_variables()}) > 1:
            decomp = decompose_equality(eq)
            decomposition_mapping[eq] = decomp
            num_impure += 1
        else:
            pure_atoms.append(eq)

    for ineq in ineqs:       
        if len({v.get_type() for v in ineq.get_free_variables()}) > 1:
            decomp = decompose_inequality(ineq)
            decomposition_mapping[ineq] = decomp
            num_impure += 1
            num_impure_ineqs += 1
        else:
            pure_atoms.append(ineq)

    def replace_with_decomp(atom) -> ExtendedFNode:
        if atom in decomposition_mapping:
            if isinstance(decomposition_mapping[atom], EqualityDecomposition):
                return decomposition_mapping[atom].pure_atoms
            elif isinstance(decomposition_mapping[atom], StrictInequalityDecomposition):
                return decomposition_mapping[atom].pure_atoms
            else:
                raise Exception("Unreachable")
        else:
            return atom

    phi_pp = map_atoms(phi_p, replace_with_decomp)

    eqs, _, ineqs = collect_atoms(phi_pp)
    n = len(eqs) + len(ineqs)
    qs = fresh_bool_vector("q_{}%s", n)
    q_mapping = {atom: qs[i] for i, atom in enumerate(eqs + ineqs) }
    skel = phi_p.substitute(q_mapping)

    intt, real, mixed = [], [], []

    for atom in eqs + ineqs:
        types = {v.get_type() for v in atom.get_free_variables()}

        if len(types) > 1:
            mixed.append(atom)
        elif typ.INT in types:
            intt.append(atom)
        else:
            real.append(atom)

    # Extend original var vectors
    v1_bridge_int_vars = fresh_int_vector("v1_bridge_{}%s", num_impure)
    v2_bridge_int_vars = fresh_int_vector("v2_bridge_{}%s", num_impure)
    w1_bridge_int_vars = fresh_int_vector("w1_bridge_{}%s", num_impure)
    w2_bridge_int_vars = fresh_int_vector("w2_bridge_{}%s", num_impure)

    v1_bridge_real_vars = fresh_real_vector("v1_bridge_{}%s", num_impure)
    v2_bridge_real_vars = fresh_real_vector("v2_bridge_{}%s", num_impure)
    w1_bridge_real_vars = fresh_real_vector("w1_bridge_{}%s", num_impure)
    w2_bridge_real_vars = fresh_real_vector("w2_bridge_{}%s", num_impure)

    int_bridge_replace_map = { decomp.int_bridge_var: Plus(v1_bridge_int_vars[i], w2_bridge_int_vars[i]) for i, decomp in enumerate(decomposition_mapping.values()) }
    real_bridge_replace_map = { decomp.real_bridge_var: Plus(v1_bridge_real_vars[i], w2_bridge_real_vars[i]) for i, decomp in enumerate(decomposition_mapping.values()) }

    v1_R = fresh_real_vector("v1_R_{}%s", num_impure_ineqs)
    v2_R = fresh_real_vector("v2_R_{}%s", num_impure_ineqs)
    w1_R = fresh_real_vector("w1_R_{}%s", num_impure_ineqs)
    w2_R = fresh_real_vector("w2_R_{}%s", num_impure_ineqs)
    
    R_replace_map = {}
    idx = 0
    for decomp in decomposition_mapping.values():
        if isinstance(decomp, StrictInequalityDecomposition):
            R_replace_map[decomp.real_dummy] = Plus(v1_R[idx], w1_R[idx])
            idx += 1

    old_int_len = len(int_vars1)
    old_real_len = len(real_vars1)

    # Extend the two original vectors
    int_vars1 += v1_bridge_int_vars + v2_bridge_int_vars
    int_vars2 += w1_bridge_int_vars + w2_bridge_int_vars
    real_vars1 += v1_bridge_real_vars + v2_bridge_real_vars + v1_R + v2_R
    real_vars2 += w1_bridge_real_vars + w2_bridge_real_vars + w1_R + w2_R

    # These vectors must align with the EXTENDED int_vars and real_vars vectors
    # First the moving cliques
    a = fresh_int_vector("a_{}%s", len(int_vars1))
    a0 = fresh_int_vector("a0_{}%s", len(int_vars1))
    
    d = fresh_real_vector("d_{}%s", len(real_vars1))
    dc = fresh_real_vector("dc_{}%s", len(real_vars1))
    dinf = fresh_real_vector("dinf_{}%s", len(real_vars1))

    # Next the static cliques
    x_int_fin = fresh_int_vector("x_ip_{}%s", orig_int_len+num_impure)
    x_real_fin = fresh_real_vector("x_rp_{}%s", orig_real_len+num_impure+num_impure_ineqs)

    finite_int_bridge_substitution = {decomp.int_bridge_var: x_int_fin[orig_int_len+i] for i, decomp in enumerate(decomposition_mapping.values())}
    finite_real_bridge_substitution = {decomp.real_bridge_var: x_real_fin[orig_real_len+i] for i, decomp in enumerate(decomposition_mapping.values())}

    finite_R_substitution = {}
    r_idx = 0
    for decomp in decomposition_mapping.values():
        if isinstance(decomp, StrictInequalityDecomposition):
            finite_R_substitution[decomp.real_dummy] = x_real_fin[orig_real_len + num_impure + r_idx]
            r_idx += 1

    # Profiles
    ## Int
    omegas = []
    ps = []

    ## Real
    rhos, sigmas, t_rhos, t_sigmas = [], [], [], []

    int_finite = []
    int_infinite = []
    for int_atom in set(intt).intersection(ineqs):
        omega1, omega2 = FreshSymbol(typ.BOOL, "o_%s"), FreshSymbol(typ.BOOL, "o_%s")
        p1, p2 = FreshSymbol(typ.BOOL, "p_%s"), FreshSymbol(typ.BOOL, "p_%s")
        ps.append(p1); ps.append(p2); omegas.append(omega1); omegas.append(omega2)
        
        int_infinite_atom = eliminate_inequality_atom_int(int_atom.substitute(int_bridge_replace_map), int_vars1, int_vars2, (omega1, omega2), (p1, p2), a, a0)
        int_finite_atom = int_atom.substitute({
            **dict(zip(int_vars1, x_int_fin)),
            **dict(zip(int_vars2, x_int_fin)),
        })

        int_finite.append(Implies(q_mapping[int_atom], int_finite_atom))
        int_infinite.append(Implies(q_mapping[int_atom], int_infinite_atom))


    real_finite = []
    real_infinite = []
    for int_atom in set(intt).intersection(eqs):
        int_infinite_atom = eliminate_eq_atom_int(int_atom.substitute(int_bridge_replace_map), int_vars1, int_vars2, a, a0)
        int_finite_atom = int_atom.substitute({
            **dict(zip(int_vars1, x_int_fin)),
            **dict(zip(int_vars2, x_int_fin)),
        })

        int_finite.append(Implies(q_mapping[int_atom], int_finite_atom))
        int_infinite.append(Implies(q_mapping[int_atom], int_infinite_atom))


    for real_atom in set(real).intersection(ineqs):
        rho, sigma = FreshSymbol(typ.REAL, "rho_%s"), FreshSymbol(typ.REAL, "sigma_%s")
        t_rho, t_sigma = FreshSymbol(typ.REAL, "trho_%s"), FreshSymbol(typ.REAL, "tsigma_%s")
        rhos.append(rho); sigmas.append(sigma); t_rhos.append(t_rho); t_sigmas.append(t_sigma)

        real_infinite_atom = eliminate_inequality_atom_real(
            real_atom.substitute({**int_bridge_replace_map, **R_replace_map}), int_vars1, int_vars2, d, dc, dinf, rho, sigma, t_rho, t_sigma)
        real_finite_atom = real_atom.substitute({
            **dict(zip(real_vars1, x_real_fin)),
            **dict(zip(real_vars2, x_real_fin)),
        })

        real_finite.append(Implies(q_mapping[real_atom], real_finite_atom))
        real_infinite.append(Implies(q_mapping[real_atom], real_infinite_atom))

    for real_atom in set(real).intersection(eqs):
        real_infinite_atom = eliminate_equality_atom_real(
            real_atom.substitute(real_bridge_replace_map), real_vars1, real_vars2, d, dc, dinf)
        real_finite_atom = real_atom.substitute({
            **dict(zip(real_vars1, x_real_fin)),
            **dict(zip(real_vars2, x_real_fin)),
        })

        real_finite.append(Implies(q_mapping[real_atom], real_finite_atom))
        real_infinite.append(Implies(q_mapping[real_atom], real_infinite_atom))

    selector = FreshSymbol(typ.INT, "s%s")

    infinite_real = Implies(Not(Equals(selector, Int(0))), And(real_infinite))
    infinite_int = Implies(Not(Equals(selector, Int(1))), And(int_infinite))

    finite_real = Implies(Equals(selector, Int(0)), And(real_finite))
    finite_int = Implies(Equals(selector, Int(1)), And(int_finite))

    clique_parts = And(infinite_real, infinite_int, finite_real, finite_int)

    int_finite_bridge = []
    real_finite_bridge = []
    mixed_bridge = []
    for i, bridge_atom in enumerate(mixed):
        int_finite_bridge += Implies(q_mapping[bridge_atom],
            eliminate_equality_atom_real(bridge_atom.substitute(
                                     real_bridge_replace_map | R_replace_map | finite_int_bridge_substitution),
                                         real_vars1, real_vars2, d, dc, dinf))
        real_finite_bridge += Implies(q_mapping[bridge_atom],
                                      eliminate_eq_atom_int(bridge_atom.substitute(
                                      int_bridge_replace_map | finite_R_substitution | finite_real_bridge_substitution),
                                                            int_vars1, int_vars2, a, a0))
        mixed_bridge += Implies(q_mapping[bridge_atom], eliminate_bridge_atom(
            v1_dc=dc[old_real_len+i],
            v2_dc=dc[old_real_len+num_impure+i],
            v1_a=a[old_int_len+i],
            w2_a=a[old_int_len+num_impure+i],
            v1_dinf=dinf[old_real_len+i],
            w2_dinf=dinf[old_real_len+num_impure+i],
            v1_a0=a0[old_int_len+i],
            w2_a0=a0[old_int_len+num_impure+i],
            v1_d0=d[old_real_len+i],
            w2_d0=d[old_real_len+num_impure+i]
        ))

    bridge_parts = And(
        Implies(Equals(selector, Int(0)), And(real_finite_bridge)),
        Implies(Equals(selector, Int(1)), And(int_finite_bridge)),
        Implies(Equals(selector, Int(2)), And(mixed_bridge)),
    )
    
    #FIXME: Restricitions are missing

    symbols = [selector] + qs + x_int_fin + x_real_fin+a0+ a+ omegas+ ps+d+ dc+ dinf+ rhos+ sigmas+ t_rhos+ t_sigmas
    return Exists(symbols,
        And(skel, clique_parts, bridge_parts)
    )
