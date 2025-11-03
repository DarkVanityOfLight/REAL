from typing import Dict, Tuple, cast

from pysmt.shortcuts import LE, LT, GT, GE, And, Equals, Exists, Int, Not, NotEquals, Or, Symbol, Plus, Times

from ramsey_extensions.fnode import ExtendedFNode
from ramsey_extensions.shortcuts import Mod, Ramsey

from ramsey_elimination.simplifications import arithmetic_solver, make_int_input_format
from ramsey_elimination.formula_utils import apply_subst, ast_to_terms, collect_atoms, contains_mod, fresh_bool_vector, fresh_int_vector, reconstruct_from_coeff_map, ensure_mod
from ramsey_elimination.existential_elimination import eliminate_existential_quantifier


FNode = ExtendedFNode # type: ignore[misc]


def eliminate_inequality_atom_int(ineq: ExtendedFNode, vars1, vars2,
                                  omega: Tuple[ExtendedFNode, ExtendedFNode],
                                  p: Tuple[ExtendedFNode, ExtendedFNode], x, x0) -> ExtendedFNode:
    assert ineq.is_lt()
    left, right = ineq.arg(0), ineq.arg(1)

    # Linearize both sides
    l_coeffs, l_const = ast_to_terms(left)
    r_coeffs, r_const = ast_to_terms(right)
    l_coeffs, r_coeffs, const = arithmetic_solver(l_coeffs, l_const, r_coeffs, r_const, set(vars1))

    # Apply substitutions
    lx   = apply_subst(l_coeffs, {vars1[i]: x[i] for i in range(len(vars1))})
    lx0  = apply_subst(l_coeffs, {vars1[i]: x0[i] for i in range(len(vars1))})
    rx0  = apply_subst(r_coeffs, {vars2[i]: x0[i] for i in range(len(vars2))})
    rx   = apply_subst({v: c for v, c in r_coeffs.items() if v in vars2}, {vars2[i]: x[i] for i in range(len(vars2))})

    # Rebuild arithmetic expressions
    left_x   = reconstruct_from_coeff_map(lx,  0, Int)
    left_x0  = reconstruct_from_coeff_map(lx0, 0, Int)
    right_x0 = reconstruct_from_coeff_map(rx0, const, Int)
    right_x  = reconstruct_from_coeff_map(rx,  0, Int)

    # Construct guarded Ramsey constraints
    g1 = Or(omega[0], And(LE(left_x0, p[0]), LE(left_x, Int(0))))
    g2 = Or(omega[1], And(LE(p[1], right_x0), GE(right_x, Int(0))))
    g3 = Or(Not(omega[1]), LT(Int(0), right_x))
    return And(g1, g2, g3)

def eliminate_mod_eq_atom_int(eq: ExtendedFNode, vars1, vars2, x, x0):
    is_negated = eq.is_not()
    eq_node = eq if not is_negated else eq.arg(0)
    left_raw, right_raw = eq_node.arg(0), eq_node.arg(1)

    # Extract modulus
    if left_raw.is_mod() and left_raw.arg(1).is_int_constant():
        e = left_raw.arg(1).constant_value()
        left_n, right_n = left_raw.arg(0), right_raw
    elif right_raw.is_mod() and right_raw.arg(1).is_int_constant():
        e = right_raw.arg(1).constant_value()
        left_n, right_n = left_raw, right_raw.arg(0)
    else:
        raise ValueError("Neither side is a mod-expression")

    left_mod  = ensure_mod(left_n, e)
    right_mod = ensure_mod(right_n, e)

    # Linearize
    l_coeffs, l_const = ast_to_terms(left_mod.arg(0))
    r_coeffs, r_const = ast_to_terms(right_mod.arg(0))
    l_coeffs, r_coeffs, const = arithmetic_solver(l_coeffs, l_const, r_coeffs, r_const, set(vars1))

    # Apply substitutions
    lx_map  = apply_subst(l_coeffs, {vars1[i]: x[i] for i in range(len(vars1))})
    lx0_map = apply_subst(l_coeffs, {vars1[i]: x0[i] for i in range(len(vars1))})
    rx_map  = apply_subst({v: c for v, c in r_coeffs.items() if v in vars2}, {vars2[i]: x[i] for i in range(len(vars2))})
    rx0_map = apply_subst(r_coeffs, {vars2[i]: x0[i] for i in range(len(vars2))})

    # Reconstruct expressions
    lx, lx0 = reconstruct_from_coeff_map(lx_map, 0, Int), reconstruct_from_coeff_map(lx0_map, 0, Int)
    rx, rx0 = reconstruct_from_coeff_map(rx_map, 0, Int), reconstruct_from_coeff_map(rx0_map, const, Int)

    def negate_if(expr): return Not(expr) if is_negated else expr

    g1 = negate_if(Equals(Mod(lx0, Int(e)), Mod(rx0, Int(e))))
    g2 = Equals(Mod(lx, Int(e)), Int(0))
    g3 = Equals(Mod(rx, Int(e)), Int(0))

    return And(g1, g2, g3)

def eliminate_eq_atom_int(eq: ExtendedFNode, vars1, vars2, x, x0):
    assert eq.is_equals()
    l_coeffs, l_const = ast_to_terms(eq.arg(0))
    r_coeffs, r_const = ast_to_terms(eq.arg(1))
    l_coeffs, r_coeffs, const = arithmetic_solver(l_coeffs, l_const, r_coeffs, r_const, set(vars1))

    # Apply substitutions
    lx_map  = apply_subst(l_coeffs, {vars1[i]: x[i] for i in range(len(vars1))})
    lx0_map = apply_subst(l_coeffs, {vars1[i]: x0[i] for i in range(len(vars1))})
    rx_map  = apply_subst({v: c for v, c in r_coeffs.items() if v in vars2}, {vars2[i]: x[i] for i in range(len(vars2))})
    rx0_map = apply_subst(r_coeffs, {vars2[i]: x0[i] for i in range(len(vars2))})

    left_x, right_x = reconstruct_from_coeff_map(lx_map, 0, Int), reconstruct_from_coeff_map(rx_map, 0, Int)
    left_x0, right_x0 = reconstruct_from_coeff_map(lx0_map, 0, Int), reconstruct_from_coeff_map(rx0_map, const, Int)

    return And(
        Equals(left_x, Int(0)),
        Equals(right_x, Int(0)),
        Equals(left_x0, right_x0)
    )

def eliminate_ramsey_int(qformula: ExtendedFNode) -> ExtendedFNode:
    """
    Modular elimination of (ramsey x y phi) quantifier.
    Uses atom-wise elimination helpers.
    """
    assert qformula.is_ramsey()
    formula = qformula.arg(0)

    # --- Collect atomic constraints ---
    eqs, modeqs, ineqs = collect_atoms(cast(ExtendedFNode, formula))
    atoms = ineqs + modeqs + eqs

    # --- Boolean abstraction ---
    qs = fresh_bool_vector("q_{}_%s", len(atoms))
    prop_skeleton = formula.substitute({atom: qs[i] for i, atom in enumerate(atoms)})

    # --- Extract Ramsey variables ---
    vars1, vars2 = cast(Tuple[Tuple[ExtendedFNode], Tuple[ExtendedFNode]], qformula.quantifier_vars())
    o = len(vars1)

    # --- New symbolic integer vectors ---
    x0 = fresh_int_vector("x0_{}_%s", o)
    x  = fresh_int_vector("x_{}_%s", o)
    x_restriction = Or([NotEquals(x[i], Int(0)) for i in range(o)])  # nontrivial x

    # --- Profile variables for inequalities ---
    p, omega = fresh_int_vector("p_{}_%s", 2*len(ineqs)), fresh_bool_vector("o_{}_%s", 2*len(ineqs))
    admissible = And([
        Or(And(Not(omega[2*i]), LT(p[2*i], p[2*i+1])), omega[2*i+1])
        for i in range(len(ineqs))
    ])

    def pairwise(seq):
        return [(seq[2*i], seq[2*i+1]) for i in range(len(seq)//2)]

    ineq_aux = list(zip(ineqs, pairwise(p), pairwise(omega)))
    ineq_iter = iter(ineq_aux)

    # --- Eliminate each atom ---
    gamma = []
    for atom in atoms:
        if atom in ineqs:
            _, p_i, omega_i = next(ineq_iter)
            gamma.append(eliminate_inequality_atom_int(atom, vars1, vars2, omega_i, p_i, x, x0))
        else:
            gamma.append(eliminate_eq_atom_int(atom, vars1, vars2, x, x0))

    # --- Guarded constraints ---
    guarded_gamma = And([Or(Not(qs[i]), gamma[i]) for i in range(len(atoms))])

    # --- Combine everything ---
    result = And(x_restriction, prop_skeleton, admissible, guarded_gamma)

    # --- Existential quantification ---
    return Exists(qs, Exists(p + omega + x + x0, result))  # type: ignore

def full_ramsey_elimination_int(formula: ExtendedFNode):
    """Performs full integer Ramsey quantifier elimination (with optional existential elimination)."""
    assert formula.is_ramsey()
    f = make_int_input_format(formula)

    # Handle nested existentials before Ramsey elimination
    if formula.arg(0).is_exists():
        f, _ = eliminate_existential_quantifier(f)

    return eliminate_ramsey_int(f)


if __name__ == "__main__":
    from ramsey_extensions.environment import push_ramsey
    from ramsey_extensions.shortcuts import *

    push_ramsey()
    get_env().enable_infix_notation = True

    # Example formula
    x = Symbol("a", INT)
    y = Symbol("b", INT)
    f = And(LT(Times(Int(2), y), Plus(x, 1)), GT(Plus(x, 1), Int(5)))
    qf = Ramsey([x], [y], f)

    print(full_ramsey_elimination_int(qf).serialize())
