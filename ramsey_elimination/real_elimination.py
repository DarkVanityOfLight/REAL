
from typing import Dict, List, Sequence, Tuple, cast

from pysmt import operators
from pysmt.shortcuts import GT, LE, LT, And, Equals, Exists, Implies, Not, Or, Plus, Real, Symbol

from ramsey_elimination.existential_elimination import eliminate_existential_quantifier
from ramsey_elimination.formula_utils import ast_to_terms, bool_vector, collect_atoms,real_vector, reconstruct_from_coeff_map
from ramsey_elimination.simplifications import apply_subst, arithmetic_solver, make_real_input_format
from ramsey_extensions.fnode import ExtendedFNode
from ramsey_extensions.operators import RAMSEY_NODE_TYPE

def not_eq_num(left, right):
    return Or(LT(left, right), GT(left, right))

def make_sub(vars_list: Sequence[ExtendedFNode], symbols_list: Sequence[ExtendedFNode]) -> Dict[ExtendedFNode, ExtendedFNode]:
    """Return a dict mapping each vars_list[i] to symbols_list[i]."""
    return { vars_list[i]: symbols_list[i] for i in range(len(vars_list)) }

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
    qs = bool_vector("q", n+m)

    prop_skeleton = formula.substitute({
        atom: qs[i]
        for i, atom in enumerate((ineqs + eqs))
    })

    # ============================
    # Profile constraints
    # ============================
    rho = real_vector("rho", n)
    sigma = real_vector("sigma", n)
    t_rho = real_vector("t_rho", n)
    t_sigma = real_vector("t_sigma", n)

    vars1, vars2 = cast(Tuple[Tuple[ExtendedFNode, ...], Tuple[ExtendedFNode, ...]], qformula.quantifier_vars())
    l = len(vars1)

    x = real_vector("x", l)
    x_c = real_vector("x_c", l)
    x_inf = real_vector("x_inf", l) 

    # Substitution maps
    sub_x_for_var1 = make_sub(vars1, x)
    sub_x_for_var2 = make_sub(vars2, x)

    sub_x_inf_for_var1 = make_sub(vars1, x_inf)
    sub_x_inf_for_var2 = make_sub(vars2, x_inf)

    sub_x_c_for_var1 = make_sub(vars1, x_c)
    sub_x_c_for_var2 = make_sub(vars2, x_c)

    lambdas, xis, deltas, mus = [None] * n, [None] * n, [None] * n, [None] * n
    z_and_h_terms: List[ExtendedFNode] = [None] * n #type: ignore
    theta_constraints = []

    for i, ineq in enumerate(ineqs):
        left, right = ineq.arg(0), ineq.arg(1)
        l_coeffs, l_const = ast_to_terms(left)
        r_coeffs, r_const = ast_to_terms(right)

        l_coeffs, r_coeffs, const = arithmetic_solver(l_coeffs, l_const, r_coeffs, r_const, set(vars1))

        # This term captures everything not related to vars1 or vars2
        wz_coeffs = {v: c for v, c in r_coeffs.items() if v not in vars2}
        z_and_h_terms[i] = reconstruct_from_coeff_map(wz_coeffs, const, Real)
        
        # rx = sy + tz + h
        rx_coeff = apply_subst(l_coeffs, sub_x_for_var1)
        rx_inf_coeff = apply_subst(l_coeffs, sub_x_inf_for_var1)
        rx_c_coeff = apply_subst(l_coeffs, sub_x_c_for_var1)

        sx_coeff = apply_subst({v:c for v,c in r_coeffs.items() if v in vars2}, sub_x_for_var2)
        sx_inf_coeff = apply_subst({v:c for v,c in r_coeffs.items() if v in vars2}, sub_x_inf_for_var2)
        sx_c_coeff = apply_subst({v:c for v,c in r_coeffs.items() if v in vars2}, sub_x_c_for_var2)

        rx = reconstruct_from_coeff_map(rx_coeff, 0, Real)
        rx_inf = reconstruct_from_coeff_map(rx_inf_coeff, 0, Real)
        sx = reconstruct_from_coeff_map(sx_coeff, 0, Real)
        sx_inf = reconstruct_from_coeff_map(sx_inf_coeff, 0, Real)
        rx_c = reconstruct_from_coeff_map(rx_c_coeff, 0, Real)
        sx_c = reconstruct_from_coeff_map(sx_c_coeff, 0, Real)

        # Lambda constraints
        lambdas[i] = And(
            Implies(
                Or(Equals(t_rho[i], Real(-1)), Equals(t_rho[i], Real(1))),
                And(Equals(rx, rho[i]), Equals(rx_inf, Real(0))),
            ),
            Implies(
                Or(Equals(t_sigma[i], Real(-1)), Equals(t_sigma[i], Real(1))),
                And(Equals(sx, sigma[i]), Equals(sx_inf, Real(0))),
            )
        )

        # Xi constraints
        xis[i] = And(
            Implies(
                Equals(t_rho[i], Real(0)),
                And(Equals(rx, rho[i]), Equals(rx_c, Real(0)), Equals(rx_inf, Real(0)))
            ),
            Implies(
                Equals(t_sigma[i], Real(0)),
                And(Equals(sx, sigma[i]), Equals(sx_c, Real(0)), Equals(sx_inf, Real(0)))
            )
        )

        # Delta constraints
        deltas[i] = And(
            Implies(Equals(t_rho[i], Real(-1)), LT(rx_c, Real(0))),
            Implies(Equals(t_rho[i], Real(1)), GT(rx_c, Real(0))),
            Implies(Equals(t_sigma[i], Real(-1)), LT(sx_c, Real(0))),
            Implies(Equals(t_sigma[i], Real(1)), GT(sx_c, Real(0))),
        )

        # Mu constraints
        mus[i] = And(
            Implies(Equals(t_rho[i], Real(-2)), LT(rx_inf, Real(0))),
            Implies(Equals(t_rho[i], Real(2)), GT(rx_inf, Real(0))),
            Implies(Equals(t_sigma[i], Real(-2)), LT(sx_inf, Real(0))),
            Implies(Equals(t_sigma[i], Real(2)), GT(sx_inf, Real(0))),
        )
        
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
            consequent1 = LT(rho[i], Plus(sigma[i], z_and_h_terms[i]))
            consequent2 = LE(rho[i], Plus(sigma[i], z_and_h_terms[i]))
            
            theta_constraints.append(Implies(antecedent1, consequent1))
            theta_constraints.append(Implies(antecedent2, consequent2))

        elif ineq_type == operators.LE:
            consequent_le = LE(rho[i], Plus(sigma[i], z_and_h_terms[i]))

            theta_constraints.append(Implies(antecedent1, consequent_le))
            theta_constraints.append(Implies(antecedent2, consequent_le))
            
        else:
            # This case should not be reached if collect_atoms is correct
            raise ValueError(f"Unexpected inequality type in loop: {ineq_type}")

    theta = And(theta_constraints)
    epsilons = [None] * m

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
            sub_x_for_var1.get(var, var): l_coeffs.get(var, 0) - v_coeffs.get(vars2[i], 0)
            for i, var in enumerate(vars1)
        }

        ux_c = reconstruct_from_coeff_map(ux_c_coeffs, 0, Real)
        ux_inf = reconstruct_from_coeff_map(ux_inf_coeffs, 0, Real)
        vx_c = reconstruct_from_coeff_map(vx_c_coeff, 0, Real)
        vx_inf = reconstruct_from_coeff_map(vx_inf_coeff, 0, Real)
        u_minus_v_x = reconstruct_from_coeff_map(u_minus_v_x_coeffs, 0, Real)
        wz_d = reconstruct_from_coeff_map(wz_coeffs, const, Real)

        epsilons[i] = And(
            Equals(ux_c, Real(0)),
            Equals(ux_inf, Real(0)),
            Equals(vx_c, Real(0)),
            Equals(vx_inf, Real(0)),
            Equals(u_minus_v_x, wz_d),
        )

    # ============================
    # Final Assembly of gamma
    # ============================
    non_trivial_xc = Or([Not(Equals(xc_i, Real(0))) for xc_i in x_c])

    ineq_implications = And([
        Implies(qs[i], And(lambdas[i], xis[i], deltas[i], mus[i]))
        for i in range(n)
    ])

    eq_implications = And([
        Implies(qs[n + i], epsilons[i])
        for i in range(m)
    ])
    
    gamma_body = And(
        prop_skeleton,
        theta,
        non_trivial_xc,
        ineq_implications,
        eq_implications
    )

    quantified_vars = qs + rho + sigma + t_rho + t_sigma + x + x_c + x_inf

    return Exists(quantified_vars, gamma_body)


def full_ramsey_elimination_real(formula: ExtendedFNode):
    assert formula.is_ramsey()

    f = make_real_input_format(formula)

    # Will introduce a new two new terms(v_0 + w_1 and distinctness) and 4 atoms for every existentially quantified variable
    if formula.arg(0).is_exists():
        f = eliminate_existential_quantifier(f)

    return eliminate_ramsey_real(f)
