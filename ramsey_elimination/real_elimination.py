
from typing import Dict, Iterable, List, Sequence, Tuple, cast

from pysmt.shortcuts import GT, LE, LT, And, Equals, Exists, Implies, Not, NotEquals, Or, Plus, Real, Symbol
from pysmt.typing import REAL, BOOL

from ramsey_elimination.formula_utils import ast_to_terms, collect_atoms, reconstruct_from_coeff_map
from ramsey_elimination.simplifications import apply_subst, arithmetic_solver
from ramsey_extensions.fnode import ExtendedFNode
from ramsey_extensions.operators import RAMSEY_NODE_TYPE
from ramsey_extensions.shortcuts import Ramsey

def not_eq_num(left, right):
    return Or(LT(left, right), GT(left, right))

def _create_real_quantifier_elimination_vars(existential_vars: Tuple[ExtendedFNode, ...]) -> Tuple[Dict[ExtendedFNode, ExtendedFNode], Tuple[ExtendedFNode, ...], Tuple[ExtendedFNode, ...], Tuple[ExtendedFNode, ...], Tuple[ExtendedFNode, ...]]:
    v1, v2, w1, w2 = [], [], [], []
    substitution_map = {}
    for i, existential_var in enumerate(existential_vars):
        assert existential_var.is_symbol(REAL)
        
        v1.append(Symbol(f"v1_{i}", REAL))
        v2.append(Symbol(f"v2_{i}", REAL))

        w1.append(Symbol(f"w1_{i}", REAL))
        w2.append(Symbol(f"w2_{i}", REAL))

        substitution_map[existential_var] = Plus(v1[i], w2[i])

    return (substitution_map, tuple(v1), tuple(v2), tuple(w1), tuple(w2))

def eliminate_real_existential_quantifiers(formula: ExtendedFNode) -> ExtendedFNode:
    assert formula.is_ramsey()
    assert formula.arg(0).is_exists()

    exvars = formula.arg(0).quantifier_vars()
    substitution_map, v1, v2, w1, w2 = _create_real_quantifier_elimination_vars(exvars)

    # Assume (ramsey (...) (...)  (exists (...) phi))
    # We extract phi
    subformula = formula.arg(0).arg(0)

    # Substitute each variable x_i bound by the existential quantifier with v1_i + w2_i
    substituted_formula = subformula.substitute(substitution_map)

    # Get the current variables bound originally by the ramsey quantifier
    x, y = cast(Tuple[Tuple[ExtendedFNode], Tuple[ExtendedFNode]], formula.quantifier_vars())

    # Add the newly introduced variables
    new_x =  x + v1 + v2
    new_y = y + w1 + w2

    #Ensure pairwise distinct subclique
    pairwise_distinct = Or([Or(LT(x[i], y[i]), LT(y[i], x[i])) for i in range(len(x))])

    # Create a new Ramsey quantifier now with the substituted formula, the pairwise distinctnes and the two new vectors of bound variables
    return Ramsey(new_x, new_y, And(substituted_formula, pairwise_distinct))


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
    qs = [Symbol(f"q_{i}", BOOL) for i in range(n + m)]

    prop_skeleton = formula.substitute({
        atom: qs[i]
        for i, atom in enumerate((ineqs + eqs))
    })

    # ============================
    # Profile constraints
    # ============================
    rho = [Symbol(f"rho_{i}") for i in range(n)]
    sigma = [Symbol(f"sigma_{i}") for i in range(n)]
    t_rho = [Symbol(f"t_rho_{i}") for i in range(n)]
    t_sigma = [Symbol(f"t_sigma_{i}") for i in range(n)]

    vars1, vars2 = cast(Tuple[Tuple[ExtendedFNode, ...], Tuple[ExtendedFNode, ...]], qformula.quantifier_vars())

    x = [Symbol(f"x_{i}", REAL) for i in range(len(vars1))]
    x_c = [Symbol(f"x_c_{i}", REAL) for i in range(len(vars1))]
    x_inf = [Symbol(f"x_inf_{i}", REAL) for i in range(len(vars1))]

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
        consequent1 = LT(rho[i], sigma[i] + z_and_h_terms[i])
        theta_constraints.append(Implies(antecedent1, consequent1))

        antecedent2 = Or(
            And(Equals(t_rho[i], Real(0)), Equals(t_sigma[i], Real(-1))),
            Equals(t_rho[i], Real(1)))
        consequent2 = LE(rho[i], Plus(sigma[i], z_and_h_terms[i]))
        theta_constraints.append(Implies(antecedent2, consequent2))

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
            sub_x_for_var1.get(var, var): l_coeffs[var] - v_coeffs.get(vars2[i], 0)
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

