from typing import Dict, Tuple, cast

from pysmt.operators import EQUALS, NOT
from pysmt.shortcuts import LE, LT, And, Equals, Exists, Int, Not, NotEquals, Or, Symbol, Plus, GE, Times
from pysmt.typing import INT

from ramsey_extensions.fnode import ExtendedFNode
from ramsey_extensions.operators import MOD_NODE_TYPE, RAMSEY_NODE_TYPE
from ramsey_extensions.shortcuts import Mod, Ramsey

from ramsey_elimination.simplifications import arithmetic_solver, make_int_input_format
from ramsey_elimination.formula_utils import apply_subst, ast_to_terms, collect_atoms, fresh_bool_vector, fresh_int_vector, reconstruct_from_coeff_map, ensure_mod
from ramsey_elimination.existential_elimination import eliminate_existential_quantifier


FNode = ExtendedFNode # type: ignore[misc]


def eliminate_ramsey_int(qformula: ExtendedFNode) -> ExtendedFNode:
    """
    Eliminates the (ramsey x y phi) quantifier from an integer formula,
    producing an equivalent formula without the Ramsey quantifier.
    """
    assert qformula.node_type() == RAMSEY_NODE_TYPE
    formula = qformula.arg(0)

    # --- Collect atomic constraints ---
    eqs, modeqs, ineqs = collect_atoms(cast(ExtendedFNode, formula))
    l, n, m = len(eqs), len(modeqs), len(ineqs)

    # --- Boolean abstraction of atoms ---
    qs = fresh_bool_vector("q_{}_%s", l + n + m)
    prop_skeleton = formula.substitute({
        atom: qs[i] for i, atom in enumerate((ineqs + modeqs + eqs))
    })

    # --- Define profile variables and constraints ---
    p, omega = fresh_int_vector("p_{}_%s", 2 * m), fresh_bool_vector("o_{}_%s", 2 * m)
    admissible = And([
        Or(
            And(Not(omega[2*i]), LT(p[2*i], p[2*i+1])),
            omega[2*i+1]
        )
        for i in range(m)
    ])

    # --- Extract Ramsey-quantified variable pairs ---
    vars1, vars2 = cast(Tuple[Tuple[ExtendedFNode], Tuple[ExtendedFNode]], qformula.quantifier_vars())
    o = len(vars1)

    # New symbolic integer vectors
    x0 = fresh_int_vector("x0_{}_%s", o)
    x = fresh_int_vector("x_{}_%s", o)
    x_restriction = Or([NotEquals(x[i], Int(0)) for i in range(o)])  # nontrivial x

    # Substitutions for variable instances
    sub1_x0 = {vars1[i]: x0[i] for i in range(o)}
    sub2_x0 = {vars2[i]: x0[i] for i in range(o)}
    sub1_x  = {vars1[i]: x[i]  for i in range(o)}
    sub2_x  = {vars2[i]: x[i]  for i in range(o)}

    gamma = []  # will hold transformed constraints

    # --- Handle inequalities ---
    for i, ineq in enumerate(ineqs):
        left, right = ineq.arg(0), ineq.arg(1)

        # Convert ASTs to coefficient maps
        l_coeffs, l_const = ast_to_terms(left)
        r_coeffs, r_const = ast_to_terms(right)

        # Align both sides into standard linear form
        l_coeffs, r_coeffs, const = arithmetic_solver(l_coeffs, l_const, r_coeffs, r_const, set(vars1))

        # Substitute variables
        lx   = apply_subst(l_coeffs, sub1_x)
        lx0  = apply_subst(l_coeffs, sub1_x0)
        rx0  = apply_subst(r_coeffs, sub2_x0)
        rx   = apply_subst({v: c for v, c in r_coeffs.items() if v in vars2}, sub2_x)

        # Reconstruct arithmetic terms
        left_x   = reconstruct_from_coeff_map(lx,  0, Int)
        left_x0  = reconstruct_from_coeff_map(lx0, 0, Int)
        right_x0 = reconstruct_from_coeff_map(rx0, const, Int)
        right_x  = reconstruct_from_coeff_map(rx,  0, Int)

        # Build guarded Ramsey constraints
        g1 = Or(omega[2*i], And(LE(left_x0, p[2*i]), LE(left_x, Int(0))))
        g2 = Or(omega[2*i+1], And(LE(p[2*i+1], right_x0), GE(right_x, Int(0))))
        g3 = Or(Not(omega[2*i+1]), LT(Int(0), right_x))
        gamma.append(And(g1, g2, g3))

    # --- Handle modular equalities ---
    for i, eq in enumerate(modeqs):
        assert eq.node_type() == EQUALS or (eq.node_type() == NOT and eq.arg(0).node_type() == EQUALS)

        is_negated = eq.node_type() == NOT
        equation = eq if not is_negated else eq.arg(0)
        left_raw, right_raw = equation.arg(0), equation.arg(1)

        # Detect modulus operand and extract modulus value
        if left_raw.node_type() == MOD_NODE_TYPE and left_raw.arg(1).is_int_constant():
            e = left_raw.arg(1).constant_value()
            left_n, right_n = left_raw.arg(0), right_raw
        elif right_raw.node_type() == MOD_NODE_TYPE and right_raw.arg(1).is_int_constant():
            e = right_raw.arg(1).constant_value()
            left_n, right_n = left_raw, right_raw.arg(0)
        else:
            raise ValueError(f"Neither side of `{equation}` is a mod‐expression")

        # Normalize both sides as mod-expressions
        left_hand_eq = ensure_mod(left_n, e)
        right_hand_eq = ensure_mod(right_n, e)

        mod = left_hand_eq.arg(1).constant_value()
        assert mod == right_hand_eq.arg(1).constant_value()

        # Linearization
        l_coeffs, l_const = ast_to_terms(left_hand_eq.arg(0))
        r_coeffs, r_const = ast_to_terms(right_hand_eq.arg(0))
        l_coeffs, r_coeffs, const = arithmetic_solver(l_coeffs, l_const, r_coeffs, r_const, set(vars1))

        # Substitute and rebuild terms
        lx_map  = apply_subst(l_coeffs, sub1_x)
        lx0_map = apply_subst(l_coeffs, sub1_x0)
        rx_map  = apply_subst({v: c for v, c in r_coeffs.items() if v in vars2}, sub2_x)
        rx0_map = apply_subst(r_coeffs, sub2_x0)

        lx, lx0 = reconstruct_from_coeff_map(lx_map, 0, Int), reconstruct_from_coeff_map(lx0_map, 0, Int)
        rx, rx0 = reconstruct_from_coeff_map(rx_map, 0, Int), reconstruct_from_coeff_map(rx0_map, const, Int)

        def negate_if(t): return Not(t) if is_negated else t

        # Modulo constraints
        g1 = negate_if(Equals(Mod(lx0, Int(mod)), Mod(rx0, Int(mod))))
        g2 = Equals(Mod(lx, Int(mod)), Int(0))
        g3 = Equals(Mod(rx, Int(mod)), Int(0))
        gamma.append(And(g1, g2, g3))

    # --- Handle equalities ---
    for i, eq in enumerate(eqs):
        l_coeffs, l_const = ast_to_terms(eq.arg(0))
        r_coeffs, r_const = ast_to_terms(eq.arg(1))
        l_coeffs, r_coeffs, const = arithmetic_solver(l_coeffs, l_const, r_coeffs, r_const, set(vars1))

        # Substitute and rebuild
        lx_map  = apply_subst(l_coeffs, sub1_x)
        lx0_map = apply_subst(l_coeffs, sub1_x0)
        rx_map  = apply_subst({v: c for v, c in r_coeffs.items() if v in vars2}, sub2_x)
        rx0_map = apply_subst(r_coeffs, sub2_x0)

        left_x, right_x = reconstruct_from_coeff_map(lx_map, 0, Int), reconstruct_from_coeff_map(rx_map, 0, Int)
        left_x0, right_x0 = reconstruct_from_coeff_map(lx0_map, 0, Int), reconstruct_from_coeff_map(rx0_map, const, Int)

        gamma.append(And(
            Equals(left_x, Int(0)),
            Equals(right_x, Int(0)),
            Equals(left_x0, right_x0)
        ))

    # --- Combine everything ---
    guarded_gamma = And([Or(Not(qs[i]), gamma[i]) for i in range(l + n + m)])
    result = And(x_restriction, prop_skeleton, admissible, guarded_gamma)

    # Return quantifier-free formula with existentially introduced params
    return Exists(qs, Exists(p + omega + x + x0, result))  # type: ignore


def full_ramsey_elimination_int(formula: ExtendedFNode):
    """Performs full integer Ramsey quantifier elimination (with optional existential elimination)."""
    assert formula.is_ramsey()
    f = make_int_input_format(formula)

    # Handle nested existentials before Ramsey elimination
    if formula.arg(0).is_exists():
        f = eliminate_existential_quantifier(f)

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
