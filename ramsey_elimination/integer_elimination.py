from typing import Dict, Tuple, cast

from pysmt.operators import EQUALS, NOT
from pysmt.shortcuts import LE, LT, And, Equals, Exists, Int, Not, NotEquals, Or, Symbol, Plus, GE, Times
from pysmt.typing import INT

from ramsey_extensions.fnode import ExtendedFNode
from ramsey_extensions.operators import MOD_NODE_TYPE, RAMSEY_NODE_TYPE
from ramsey_extensions.shortcuts import Mod, Ramsey

from ramsey_elimination.simplifications import arithmetic_solver, make_int_input_format, apply_subst
from ramsey_elimination.formula_utils import ast_to_terms,collect_atoms, fresh_bool_vector, fresh_int_vector, reconstruct_from_coeff_map, ensure_mod
from ramsey_elimination.existential_elimination import eliminate_existential_quantifier


FNode = ExtendedFNode # type: ignore[misc]

def eliminate_ramsey_int(qformula: ExtendedFNode) -> ExtendedFNode:
    """
    Eliminate the (ramsey x y phi) quantifier from a formula.
    Returns an equivalent formula without the Ramsey quantifier.
    """
    assert qformula.node_type() == RAMSEY_NODE_TYPE
    formula = qformula.arg(0)

    # ============================
    # Collect atoms
    # ============================
    eqs, modeqs, ineqs = collect_atoms(cast(ExtendedFNode, formula))
    l, n, m = len(eqs), len(modeqs), len(ineqs)

    # ============================
    # Boolean abstraction
    # ============================
    qs = fresh_bool_vector("q_{}_%s", l+n+m)

    prop_skeleton = formula.substitute({
        atom: qs[i]
        for i, atom in enumerate((ineqs + modeqs + eqs))
    })

    # ============================
    # Profile constraints
    # ============================
    p, omega = fresh_int_vector("p_{}_%s", 2*m), fresh_bool_vector("o_{}_%s", 2*m)

    admissible = And([
        Or(
            And(Not(omega[2*i]), LT(p[2*i], p[2*i+1])),
            omega[2*i+1]
        )
        for i in range(m)
    ])

    # ============================
    # Parametrize variables
    # ============================
    vars1, vars2 = cast(Tuple[Tuple[ExtendedFNode], Tuple[ExtendedFNode]], qformula.quantifier_vars())
    o = len(vars1)

    x0 = fresh_int_vector("x0_{}_%s", o)
    x = fresh_int_vector("x_{}_%s", o)
    x_restriction = Or([NotEquals(x[i], Int(0)) for i in range(o)])

    sub1_x0= {vars1[i]: x0[i] for i in range(o)}
    sub2_x0 = {vars2[i]: x0[i] for i in range(o)}
    sub1_x  = {vars1[i]: x[i] for i in range(o)}
    sub2_x  = {vars2[i]: x[i] for i in range(o)}

    # ============================
    # Handle inequalities
    # ============================
    gamma = []

    for i, ineq in enumerate(ineqs):

        # r x = sy + tz + h

        left, right = ineq.arg(0), ineq.arg(1)
        l_coeffs, l_const = ast_to_terms(left)
        r_coeffs, r_const = ast_to_terms(right)

        l_coeffs, r_coeffs, const = arithmetic_solver(l_coeffs, l_const, r_coeffs, r_const, set(vars1))


        lx = apply_subst(l_coeffs, sub1_x) # r x
        lx0 = apply_subst(l_coeffs, sub1_x0) # r x0
        rx0 = apply_subst(r_coeffs, sub2_x0) # s x0 + tz + h
        rx  = apply_subst({v:c for v,c in r_coeffs.items() if v in vars2}, sub2_x) # sx

        left_x   = reconstruct_from_coeff_map(lx,  0, Int) #type: ignore
        left_x0  = reconstruct_from_coeff_map(lx0, 0, Int) #type: ignore
        right_x0 = reconstruct_from_coeff_map(rx0, const, Int) #type: ignore
        right_x  = reconstruct_from_coeff_map(rx,  0, Int) #type: ignore


        g1 = Or(omega[2*i], And(LE(left_x0, p[2*i]), LE(left_x, Int(0))))
        g2 = Or(omega[2*i+1], And(LE(p[2*i+1], right_x0), GE(right_x, Int(0))))
        g3 = Or(Not(omega[2*i+1]), LT(Int(0), right_x))

        gamma.append(And(g1, g2, g3))

    # ============================
    # Handle mod equalities
    # ============================
    for i, eq in enumerate(modeqs):
        assert eq.node_type() == EQUALS or (eq.node_type() == NOT and eq.arg(0).node_type() == EQUALS)

        # !(ux % e = vy + wz + d % e)
        # ux % e = vy + wz + d % e

        is_negated = eq.node_type() == NOT
        equation = eq if not is_negated else eq.arg(0)
        left_raw = equation.arg(0)
        right_raw = equation.arg(1)
        if left_raw.node_type() == MOD_NODE_TYPE and left_raw.arg(1).is_int_constant():
            e      = left_raw.arg(1).constant_value()
            left_n = left_raw.arg(0)
            right_n= right_raw
        elif right_raw.node_type() == MOD_NODE_TYPE and right_raw.arg(1).is_int_constant():
            e       = right_raw.arg(1).constant_value()
            right_n = right_raw.arg(0)
            left_n  = left_raw
        else:
            raise ValueError(f"Neither side of `{equation}` is a mod‐expression")

        left_hand_eq: ExtendedFNode = ensure_mod(left_n, e)
        right_hand_eq: ExtendedFNode = ensure_mod(right_n, e)

        # Peel of mod
        assert left_hand_eq.node_type() == MOD_NODE_TYPE
        assert left_hand_eq.arg(1).is_int_constant()
        assert right_hand_eq.node_type() == MOD_NODE_TYPE
        assert right_hand_eq.arg(1).is_int_constant()

        mod = left_hand_eq.arg(1).constant_value()
        assert mod == right_hand_eq.arg(1).constant_value() 

        # Construct atoms
        l_coeffs, l_const = ast_to_terms(left_hand_eq.arg(0))
        r_coeffs, r_const = ast_to_terms(right_hand_eq.arg(0))
        l_coeffs, r_coeffs, const = arithmetic_solver(l_coeffs, l_const, r_coeffs, r_const, set(vars1))

        lx_map = apply_subst(l_coeffs, sub1_x) # u x
        lx0_map = apply_subst(l_coeffs, sub1_x0) # u x0
        rx0_map = apply_subst(r_coeffs, sub2_x0) # v x0 + wz
        rx_map  = apply_subst({v:c for v,c in r_coeffs.items() if v in vars2}, sub2_x) # vx

        lx = reconstruct_from_coeff_map(lx_map, 0, Int) #type: ignore
        lx0 = reconstruct_from_coeff_map(lx0_map, 0, Int) #type: ignore
        rx0 = reconstruct_from_coeff_map(rx0_map, const, Int) # v x0 + wz + d  #type: ignore
        rx = reconstruct_from_coeff_map(rx_map, 0, Int) # vx  #type: ignore

        def negate_if(t): return Not(t) if is_negated else t

        g1 = negate_if(Equals(Mod(lx0, Int(mod)), Mod(rx0, Int(mod))))# u x0 % e = v x0 + wz + d % e
        g2 = Equals(Mod(lx, Int(mod)), Int(0))# u x % e = 0 % e
        g3 = Equals(Mod(rx, Int(mod)), Int(0))# vx %e = 0 % e

        gamma.append(And(g1, g2, g3))

    # ============================
    # Handle equalities
    # ============================
    for i, eq in enumerate(eqs):

        l_coeffs, l_const = ast_to_terms(eq.arg(0))
        r_coeffs, r_const = ast_to_terms(eq.arg(1))
        l_coeffs, r_coeffs, const = arithmetic_solver(l_coeffs, l_const, r_coeffs, r_const, set(vars1))

        # rx = sy + tz + h

        lx_map = apply_subst(l_coeffs, sub1_x) # rx
        lx0_map = apply_subst(l_coeffs, sub1_x0) # r x0
        rx_map  = apply_subst({v:c for v,c in r_coeffs.items() if v in vars2}, sub2_x) # sx
        rx0_map = apply_subst(r_coeffs,  sub2_x0) # s x0 + tz

        left_x = reconstruct_from_coeff_map(lx_map, 0, Int) #type: ignore
        right_x = reconstruct_from_coeff_map(rx_map, 0, Int) #type: ignore
        left_x0 = reconstruct_from_coeff_map(lx0_map, 0, Int) #type: ignore
        right_x0 = reconstruct_from_coeff_map(rx0_map, const, Int) # s x0 + tz + h #type: ignore

        gamma.append(And(
            Equals(left_x, Int(0)), # rx = 0
            Equals(right_x, Int(0)), # vx = 0
            Equals(left_x0, right_x0) # r x_0 = s x0 + tz + h
        ))

    # ============================
    # Final assembly
    # ============================
    guarded_gamma = And([Or(Not(qs[i]), gamma[i]) for i in range(l + n + m)])

    result = And(x_restriction, prop_skeleton, admissible, guarded_gamma)

    return Exists(qs, Exists(p + omega + x + x0, result))  #type: ignore
    

def full_ramsey_elimination_int(formula: ExtendedFNode):
    assert formula.is_ramsey()

    f = make_int_input_format(formula)

    # Will introduce a new two new terms(v_0 + w_1 and distinctness) and 4 atoms for every existentially quantified variable
    if formula.arg(0).is_exists():
        f = eliminate_existential_quantifier(f)

    return eliminate_ramsey_int(f)




if __name__ == "__main__":
    from ramsey_extensions.environment import push_ramsey
    from ramsey_extensions.shortcuts import *

    push_ramsey()
    get_env().enable_infix_notation = True

    x = Symbol("a", INT)
    y = Symbol("b", INT)
    f =  And(LT(Times(Int(2), y), Plus(x, 1)), GT(Plus(x, 1), Int(5))) # And(Int(2)*y <= x, x >= Int(5))
    qf = Ramsey([x], [y], f)

    print(full_ramsey_elimination_int(qf).serialize())





