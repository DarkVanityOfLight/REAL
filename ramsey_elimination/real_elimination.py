from typing import Tuple, cast

from pysmt.shortcuts import GT, LE, LT, And, Equals, Exists, Implies, Not, Or, Plus, Real

from ramsey_elimination.existential_elimination import eliminate_existential_quantifier
from ramsey_elimination.formula_utils import apply_subst, ast_to_terms, collect_atoms, fresh_bool_vector, fresh_real_vector, reconstruct_from_coeff_map
from ramsey_elimination.simplifications import arithmetic_solver, make_real_input_format
from ramsey_extensions.fnode import ExtendedFNode

FNode = ExtendedFNode # type: ignore[misc]

def eliminate_inequality_atom_real(
    ineq: ExtendedFNode,
    vars1, vars2,
    x, x_c, x_inf,
    rho_i, sigma_i, t_rho_i, t_sigma_i,
) -> ExtendedFNode:
    assert ineq.is_lt() or ineq.is_le()
    left, right = ineq.arg(0), ineq.arg(1)
    l_coeffs, l_const = ast_to_terms(left)
    r_coeffs, r_const = ast_to_terms(right)
    l_coeffs, r_coeffs, const = arithmetic_solver(l_coeffs, l_const, r_coeffs, r_const, set(vars1))

    wz_coeffs = {v: c for v, c in r_coeffs.items() if v not in vars2}
    z_and_h_term = reconstruct_from_coeff_map(wz_coeffs, const, Real)  # type: ignore

    rx_coeff = apply_subst(l_coeffs, dict(zip(vars1, x)))
    rx_c_coeff = apply_subst(l_coeffs, dict(zip(vars1, x_c)))
    rx_inf_coeff = apply_subst(l_coeffs, dict(zip(vars1, x_inf)))

    sx_coeff = apply_subst({v: c for v, c in r_coeffs.items() if v in vars2}, dict(zip(vars2, x)))
    sx_c_coeff = apply_subst({v: c for v, c in r_coeffs.items() if v in vars2}, dict(zip(vars2, x_c)))
    sx_inf_coeff = apply_subst({v: c for v, c in r_coeffs.items() if v in vars2}, dict(zip(vars2, x_inf)))

    rx = reconstruct_from_coeff_map(rx_coeff, 0, Real)  # type: ignore
    rx_c = reconstruct_from_coeff_map(rx_c_coeff, 0, Real)  # type: ignore
    rx_inf = reconstruct_from_coeff_map(rx_inf_coeff, 0, Real)  # type: ignore
    sx = reconstruct_from_coeff_map(sx_coeff, 0, Real)  # type: ignore
    sx_c = reconstruct_from_coeff_map(sx_c_coeff, 0, Real)  # type: ignore
    sx_inf = reconstruct_from_coeff_map(sx_inf_coeff, 0, Real)  # type: ignore

    lambdas = And(
        Implies(Or(Equals(t_rho_i, Real(-1)), Equals(t_rho_i, Real(1))),
                And(Equals(rx, rho_i), Equals(rx_inf, Real(0)))),
        Implies(Or(Equals(t_sigma_i, Real(-1)), Equals(t_sigma_i, Real(1))),
                And(Equals(sx, sigma_i), Equals(sx_inf, Real(0))))
    )

    xis = And(
        Implies(Equals(t_rho_i, Real(0)), And(Equals(rx, rho_i), Equals(rx_c, Real(0)), Equals(rx_inf, Real(0)))),
        Implies(Equals(t_sigma_i, Real(0)), And(Equals(sx, sigma_i), Equals(sx_c, Real(0)), Equals(sx_inf, Real(0))))
    )

    deltas = And(
        Implies(Equals(t_rho_i, Real(-1)), LT(rx_c, Real(0))),
        Implies(Equals(t_rho_i, Real(1)), GT(rx_c, Real(0))),
        Implies(Equals(t_sigma_i, Real(-1)), LT(sx_c, Real(0))),
        Implies(Equals(t_sigma_i, Real(1)), GT(sx_c, Real(0))),
    )

    mus = And(
        Implies(Equals(t_rho_i, Real(-2)), LT(rx_inf, Real(0))),
        Implies(Equals(t_rho_i, Real(2)), GT(rx_inf, Real(0))),
        Implies(Equals(t_sigma_i, Real(-2)), LT(sx_inf, Real(0))),
        Implies(Equals(t_sigma_i, Real(2)), GT(sx_inf, Real(0))),
    )

    theta = And(
        Or([Equals(t_rho_i, Real(v)) for v in [-2, -1, 0, 1, 2]]),
        Or([Equals(t_sigma_i, Real(v)) for v in [-1, 0, 1, 2]]),
        Implies(Equals(t_rho_i, Real(2)), Equals(t_sigma_i, Real(2)))
    )

    antecedent1 = Or(
        And(Or(Equals(t_rho_i, Real(-1)), Equals(t_rho_i, Real(0))),
            Or(Equals(t_sigma_i, Real(0)), Equals(t_sigma_i, Real(1)))),
        And(Equals(t_rho_i, Real(-1)), Equals(t_sigma_i, Real(-1)))
    )
    antecedent2 = Or(
        And(Equals(t_rho_i, Real(0)), Equals(t_sigma_i, Real(-1))),
        Equals(t_rho_i, Real(1))
    )

    if ineq.is_lt():
        cons1 = LT(rho_i, Plus(sigma_i, z_and_h_term))
        cons2 = LE(rho_i, Plus(sigma_i, z_and_h_term))
        theta = And(theta, Implies(antecedent1, cons1), Implies(antecedent2, cons2))
    elif ineq.is_le():
        cons_le = LE(rho_i, Plus(sigma_i, z_and_h_term))
        theta = And(theta, Implies(Or(antecedent1, antecedent2), cons_le))

    return And(lambdas, xis, deltas, mus, theta)

def eliminate_equality_atom_real(
    eq: ExtendedFNode,
    vars1, vars2,
    x_c, x_inf
) -> ExtendedFNode:
    assert eq.is_equals()
    left, right = eq.arg(0), eq.arg(1)
    l_coeffs, l_const = ast_to_terms(left)
    r_coeffs, r_const = ast_to_terms(right)
    l_coeffs, r_coeffs, const = arithmetic_solver(l_coeffs, l_const, r_coeffs, r_const, set(vars1))

    ux_c_coeffs = apply_subst(l_coeffs, dict(zip(vars1, x_c)))
    ux_inf_coeffs = apply_subst(l_coeffs, dict(zip(vars1, x_inf)))

    v_coeffs = {v: c for v, c in r_coeffs.items() if v in vars2}
    vx_c_coeff = apply_subst(v_coeffs, dict(zip(vars2, x_c)))
    vx_inf_coeff = apply_subst(v_coeffs, dict(zip(vars2, x_inf)))

    wz_coeffs = {v: c for v, c in r_coeffs.items() if v not in vars2}
    u_minus_v_x_coeffs = {
        dict(zip(vars1, x_c)).get(v1, v1): l_coeffs.get(v1, 0) - v_coeffs.get(v2, 0)
        for v1, v2 in zip(vars1, vars2)
    }

    ux_c = reconstruct_from_coeff_map(ux_c_coeffs, 0, Real)  # type: ignore
    ux_inf = reconstruct_from_coeff_map(ux_inf_coeffs, 0, Real)  # type: ignore
    vx_c = reconstruct_from_coeff_map(vx_c_coeff, 0, Real)  # type: ignore
    vx_inf = reconstruct_from_coeff_map(vx_inf_coeff, 0, Real)  # type: ignore
    u_minus_v_x = reconstruct_from_coeff_map(u_minus_v_x_coeffs, 0, Real)  # type: ignore
    wz_d = reconstruct_from_coeff_map(wz_coeffs, const, Real)  # type: ignore

    return And(
        Equals(ux_c, Real(0)),
        Equals(ux_inf, Real(0)),
        Equals(vx_c, Real(0)),
        Equals(vx_inf, Real(0)),
        Equals(u_minus_v_x, wz_d),
    )

def eliminate_ramsey_real(qformula: ExtendedFNode) -> ExtendedFNode:
    assert qformula.is_ramsey()
    formula: ExtendedFNode = qformula.arg(0)

    eqs, _, ineqs = collect_atoms(formula)
    n, m = len(ineqs), len(eqs)
    qs = fresh_bool_vector("q_{}_%s", n + m)
    prop_skeleton = formula.substitute({atom: qs[i] for i, atom in enumerate(ineqs + eqs)})

    vars1, vars2 = cast(Tuple[Tuple[ExtendedFNode, ...], Tuple[ExtendedFNode, ...]], qformula.quantifier_vars())
    l = len(vars1)

    rho, sigma = fresh_real_vector("rho_{}_%s", n), fresh_real_vector("sigma_{}_%s", n)
    t_rho, t_sigma = fresh_real_vector("t_rho_{}_%s", n), fresh_real_vector("t_sigma_{}_%s", n)
    x, x_c, x_inf = (
        fresh_real_vector("x_{}_%s", l),
        fresh_real_vector("x_c_{}_%s", l),
        fresh_real_vector("x_inf_{}_%s", l),
    )

    gamma = []

    for i, ineq in enumerate(ineqs):
        gamma.append(
            Implies(
                qs[i],
                eliminate_inequality_atom_real(ineq, vars1, vars2, x, x_c, x_inf, rho[i], sigma[i], t_rho[i], t_sigma[i])
            )
        )

    for j, eq in enumerate(eqs):
        gamma.append(
            Implies(qs[n + j], eliminate_equality_atom_real(eq, vars1, vars2, x_c, x_inf))
        )

    non_trivial_xc = Or([Not(Equals(xc_i, Real(0))) for xc_i in x_c])
    gamma_body = And(prop_skeleton, And(gamma), non_trivial_xc)
    quantified_vars = qs + rho + sigma + t_rho + t_sigma + x + x_c + x_inf
    return Exists(quantified_vars, gamma_body)  # type: ignore

def full_ramsey_elimination_real(formula: ExtendedFNode):
    """Perform Ramsey elimination on a real-valued formula, including pre-processing."""
    assert formula.is_ramsey()
    f = make_real_input_format(formula)

    # Eliminate inner existential quantifiers if present
    if formula.arg(0).is_exists():
        f = eliminate_existential_quantifier(f)

    return eliminate_ramsey_real(f)
