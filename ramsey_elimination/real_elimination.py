from typing import List, Optional, Tuple, cast

from pysmt import operators
from pysmt.shortcuts import GT, LE, LT, And, Equals, Exists, Implies, Not, Or, Plus, Real

from ramsey_elimination.existential_elimination import eliminate_existential_quantifier
from ramsey_elimination.formula_utils import apply_subst, ast_to_terms, collect_atoms, fresh_bool_vector, fresh_real_vector, reconstruct_from_coeff_map
from ramsey_elimination.simplifications import arithmetic_solver, make_real_input_format
from ramsey_extensions.fnode import ExtendedFNode
from ramsey_extensions.operators import RAMSEY_NODE_TYPE

FNode = ExtendedFNode # type: ignore[misc]

def not_eq_num(left, right):
    return Or(LT(left, right), GT(left, right))

def eliminate_ramsey_real(qformula: ExtendedFNode) -> ExtendedFNode:
    """
    Eliminate the (ramsey x y phi) quantifier from a formula.
    Returns an equivalent formula without the Ramsey quantifier.
    """
    assert qformula.node_type() == RAMSEY_NODE_TYPE
    formula = qformula.arg(0)

    # ============================
    # Collect atoms
    # ============================
    eqs, _, ineqs = collect_atoms(cast(ExtendedFNode, formula))  # There are no mod equalitys
    n, m = len(ineqs), len(eqs)

    # ============================
    # Boolean abstraction
    # ============================
    qs = fresh_bool_vector("q_{}_%s", n+m)

    prop_skeleton = formula.substitute({
        atom: qs[i]
        for i, atom in enumerate((ineqs + eqs))
    })

    # ============================
    # Profile constraints
    # ============================
    rho = fresh_real_vector("rho_{}_%s", n)
    sigma = fresh_real_vector("sigma_{}_%s", n)
    t_rho = fresh_real_vector("t_rho_{}_%s", n)
    t_sigma = fresh_real_vector("t_sigma_{}_%s", n)

    vars1, vars2 = cast(Tuple[Tuple[ExtendedFNode, ...], Tuple[ExtendedFNode, ...]], qformula.quantifier_vars())
    l = len(vars1)

    x = fresh_real_vector("x_{}_%s", l)
    x_c = fresh_real_vector("x_c_{}_%s", l)
    x_inf = fresh_real_vector("x_inf_{}_%s", l) 

    # Substitution maps
    sub_x_for_var1 = dict(zip(vars1, x))
    sub_x_for_var2 = dict(zip(vars2, x))

    sub_x_inf_for_var1 = dict(zip(vars1, x_inf))
    sub_x_inf_for_var2 = dict(zip(vars2, x_inf))

    sub_x_c_for_var1 = dict(zip(vars1, x_c))
    sub_x_c_for_var2 = dict(zip(vars2, x_c))

    # Profile variables
    lambdas: List[Optional[ExtendedFNode]] = [None] * n
    xis: List[Optional[ExtendedFNode]] = [None] * n
    deltas: List[Optional[ExtendedFNode]] = [None] * n
    mus: List[Optional[ExtendedFNode]] = [None] * n
    theta_constraints = []
    ineq_implications: List[Optional[ExtendedFNode]] = [None] * n

    for i, ineq in enumerate(ineqs):
        left, right = ineq.arg(0), ineq.arg(1)
        l_coeffs, l_const = ast_to_terms(left)
        r_coeffs, r_const = ast_to_terms(right)

        l_coeffs, r_coeffs, const = arithmetic_solver(l_coeffs, l_const, r_coeffs, r_const, set(vars1))

        # This term captures everything not related to vars1 or vars2
        wz_coeffs = {v: c for v, c in r_coeffs.items() if v not in vars2}
        z_and_h_term = reconstruct_from_coeff_map(wz_coeffs, const, Real) #type: ignore
        
        # rx = sy + tz + h
        rx_coeff = apply_subst(l_coeffs, sub_x_for_var1)
        rx_inf_coeff = apply_subst(l_coeffs, sub_x_inf_for_var1)
        rx_c_coeff = apply_subst(l_coeffs, sub_x_c_for_var1)

        sx_coeff = apply_subst({v:c for v,c in r_coeffs.items() if v in vars2}, sub_x_for_var2)
        sx_inf_coeff = apply_subst({v:c for v,c in r_coeffs.items() if v in vars2}, sub_x_inf_for_var2)
        sx_c_coeff = apply_subst({v:c for v,c in r_coeffs.items() if v in vars2}, sub_x_c_for_var2)

        rx = reconstruct_from_coeff_map(rx_coeff, 0, Real) #type: ignore
        rx_inf = reconstruct_from_coeff_map(rx_inf_coeff, 0, Real) #type: ignore
        sx = reconstruct_from_coeff_map(sx_coeff, 0, Real) #type: ignore
        sx_inf = reconstruct_from_coeff_map(sx_inf_coeff, 0, Real) #type: ignore
        rx_c = reconstruct_from_coeff_map(rx_c_coeff, 0, Real) #type: ignore
        sx_c = reconstruct_from_coeff_map(sx_c_coeff, 0, Real) #type: ignore

        # Lambda constraints
        lambdas[i] = cast(ExtendedFNode, And(
            Implies(
                Or(Equals(t_rho[i], Real(-1)), Equals(t_rho[i], Real(1))),
                And(Equals(rx, rho[i]), Equals(rx_inf, Real(0))),
            ),
            Implies(
                Or(Equals(t_sigma[i], Real(-1)), Equals(t_sigma[i], Real(1))),
                And(Equals(sx, sigma[i]), Equals(sx_inf, Real(0))),
            )
        ))

        # Xi constraints
        xis[i] = cast(ExtendedFNode, And(
            Implies(
                Equals(t_rho[i], Real(0)),
                And(Equals(rx, rho[i]), Equals(rx_c, Real(0)), Equals(rx_inf, Real(0)))
            ),
            Implies(
                Equals(t_sigma[i], Real(0)),
                And(Equals(sx, sigma[i]), Equals(sx_c, Real(0)), Equals(sx_inf, Real(0)))
            )
        ))

        # Delta constraints
        deltas[i] = cast(ExtendedFNode, And(
            Implies(Equals(t_rho[i], Real(-1)), LT(rx_c, Real(0))),
            Implies(Equals(t_rho[i], Real(1)), GT(rx_c, Real(0))),
            Implies(Equals(t_sigma[i], Real(-1)), LT(sx_c, Real(0))),
            Implies(Equals(t_sigma[i], Real(1)), GT(sx_c, Real(0))),
        ))

        # Mu constraints
        mus[i] = cast(ExtendedFNode, And(
            Implies(Equals(t_rho[i], Real(-2)), LT(rx_inf, Real(0))),
            Implies(Equals(t_rho[i], Real(2)), GT(rx_inf, Real(0))),
            Implies(Equals(t_sigma[i], Real(-2)), LT(sx_inf, Real(0))),
            Implies(Equals(t_sigma[i], Real(2)), GT(sx_inf, Real(0))),
        ))
        
        # Theta constraints
        theta_constraints.append(Or([Equals(t_rho[i], Real(v)) for v in [-2, -1, 0, 1, 2]]))
        theta_constraints.append(Or([Equals(t_sigma[i], Real(v)) for v in [-1, 0, 1, 2]]))
        theta_constraints.append(Implies(Equals(t_rho[i], Real(2)), Equals(t_sigma[i], Real(2))))

        antecedent1 = Or(
            And(Or(Equals(t_rho[i], Real(-1)), Equals(t_rho[i], Real(0))),
                Or(Equals(t_sigma[i], Real(0)), Equals(t_sigma[i], Real(1)))),
            And(Equals(t_rho[i], Real(-1)), Equals(t_sigma[i], Real(-1))))

        antecedent2 = Or(
            And(Equals(t_rho[i], Real(0)), Equals(t_sigma[i], Real(-1))),
            Equals(t_rho[i], Real(1)))

        ineq_type = ineq.node_type()
        if ineq_type == operators.LT:
            consequent1 = LT(rho[i], Plus(sigma[i], z_and_h_term))
            consequent2 = LE(rho[i], Plus(sigma[i], z_and_h_term))
            
            theta_constraints.append(Implies(antecedent1, consequent1))
            theta_constraints.append(Implies(antecedent2, consequent2))

        elif ineq_type == operators.LE:
            consequent_le = LE(rho[i], Plus(sigma[i], z_and_h_term))
            theta_constraints.append(Implies(Or(antecedent1, antecedent2), consequent_le))
        else:
            # This case should not be reached if collect_atoms is correct
            raise ValueError(f"Unexpected inequality type in loop: {ineq_type}")


        ineq_implications[i] = cast(ExtendedFNode, Implies(qs[i], And(lambdas[i], xis[i], deltas[i], mus[i])))

    theta = And(theta_constraints)
    epsilons: List[Optional[ExtendedFNode]] = [None] * m

    for i, eq in enumerate(eqs):
        left, right = eq.arg(0), eq.arg(1)
        l_coeffs, l_const = ast_to_terms(left)
        r_coeffs, r_const = ast_to_terms(right)

        l_coeffs, r_coeffs, const = arithmetic_solver(l_coeffs, l_const, r_coeffs, r_const, set(vars1))

        # ux = vy + wz + d
        ux_c_coeffs = apply_subst(l_coeffs, sub_x_c_for_var1)
        ux_inf_coeffs = apply_subst(l_coeffs, sub_x_inf_for_var1)

        v_coeffs = {v:c for v,c in r_coeffs.items() if v in vars2}
        vx_c_coeff = apply_subst(v_coeffs, sub_x_c_for_var2)
        vx_inf_coeff = apply_subst(v_coeffs, sub_x_inf_for_var2)

        wz_coeffs = {v: c for v, c in r_coeffs.items() if v not in vars2}

        u_minus_v_x_coeffs = {
            sub_x_for_var1.get(var1, var1): l_coeffs.get(var1, 0) - v_coeffs.get(var2, 0)
            for var1, var2 in zip(vars1, vars2)
        }

        ux_c = reconstruct_from_coeff_map(ux_c_coeffs, 0, Real) #type: ignore
        ux_inf = reconstruct_from_coeff_map(ux_inf_coeffs, 0, Real) #type: ignore
        vx_c = reconstruct_from_coeff_map(vx_c_coeff, 0, Real) #type: ignore
        vx_inf = reconstruct_from_coeff_map(vx_inf_coeff, 0, Real) #type: ignore
        u_minus_v_x = reconstruct_from_coeff_map(u_minus_v_x_coeffs, 0, Real) #type: ignore
        wz_d = reconstruct_from_coeff_map(wz_coeffs, const, Real) #type: ignore

        epsilons[i] = cast(ExtendedFNode, And(
            Equals(ux_c, Real(0)),
            Equals(ux_inf, Real(0)),
            Equals(vx_c, Real(0)),
            Equals(vx_inf, Real(0)),
            Equals(u_minus_v_x, wz_d),
        ))

    # ============================
    # Final Assembly of gamma
    # ============================
    non_trivial_xc = Or([Not(Equals(xc_i, Real(0))) for xc_i in x_c])

    eq_implications = And([
        Implies(qs[n + i], epsilons[i])
        for i in range(m)
    ])
    
    gamma_body = And(
        prop_skeleton,
        theta,
        non_trivial_xc,
        And(ineq_implications),
        eq_implications
    )

    quantified_vars = qs + rho + sigma + t_rho + t_sigma + x + x_c + x_inf

    return Exists(quantified_vars, gamma_body) #type: ignore


def full_ramsey_elimination_real(formula: ExtendedFNode):
    """Perform Ramsey elimination on a real-valued formula, including pre-processing."""
    assert formula.is_ramsey()
    f = make_real_input_format(formula)

    # Eliminate inner existential quantifiers if present
    if formula.arg(0).is_exists():
        f = eliminate_existential_quantifier(f)

    return eliminate_ramsey_real(f)
