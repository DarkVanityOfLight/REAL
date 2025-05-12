from pysmt.operators import EQUALS, NOT
from pysmt.shortcuts import LE, LT, And, Equals, Exists, Int, Not, NotEquals, Or, Symbol, Plus, GE
from pysmt.typing import INT, BOOL
from RamseyQuantors.fnode import ExtendedFNode
from RamseyQuantors.operators import MOD_NODE_TYPE, RAMSEY_NODE_TYPE

from typing import Dict, Tuple, cast, Optional

from RamseyQuantors.shortcuts import Mod, Ramsey
from RamseyQuantors.simplifications import arithmetic_solver, collect_sum_terms, int_inequality_rewriter, push_negations_inside

from RamseyQuantors.formula_utils import collect_atoms, collect_subterms_of_var, reconstruct_from_coeff_map, split_left_right



def _create_integer_quantifier_elimination_vars(existential_vars: Tuple[ExtendedFNode, ...]) -> Tuple[Dict[ExtendedFNode, ExtendedFNode], Tuple[ExtendedFNode, ...], Tuple[ExtendedFNode, ...], Tuple[ExtendedFNode, ...], Tuple[ExtendedFNode, ...]]:

    v1, v2, w1, w2 = [], [], [], []
    substitution_map = {}
    for i, existential_var in enumerate(existential_vars):
        assert existential_var.is_symbol(INT)
        
        v1.append(Symbol(f"v1_{i}", INT))
        v2.append(Symbol(f"v2_{i}", INT))

        w1.append(Symbol(f"w1_{i}", INT))
        w2.append(Symbol(f"w2_{i}", INT))

        substitution_map[existential_var] = Plus(v1[i], w2[i])

    return (substitution_map, tuple(v1), tuple(v2), tuple(w1), tuple(w2))


def eliminate_integer_existential_quantifiers(formula: ExtendedFNode) -> ExtendedFNode:
    assert formula.is_ramsey()
    assert formula.arg(0).is_exists()

    exvars = formula.arg(0).quantifier_vars()
    substitution_map, v1, v2, w1, w2 = _create_integer_quantifier_elimination_vars(exvars)

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
    pairwise_distinct = Or([Or(x[i] < y[i], y[i] < x[i]) for i in range(len(x))])

    # Create a new Ramsey quantifier now with the substituted formula, the pairwise distinctnes and the two new vectors of bound variables
    return Ramsey(new_x, new_y, And(substituted_formula, pairwise_distinct))


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
    qs = [Symbol(f"q_{i}", BOOL) for i in range(l + n + m)]

    prop_skeleton = formula.substitute({
        atom: qs[i]
        for i, atom in enumerate(eqs + modeqs + ineqs)
    })

    # ============================
    # Profile constraints
    # ============================
    p, omega = [Symbol(f"p_{i}", INT) for i in range(2*m)], [Symbol(f"o_{i}", BOOL) for i in range(2*m)]

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

    x0 = [Symbol(f"x0_{i}", INT) for i in range(o)]
    x = [Symbol(f"x_{i}", INT) for i in range(o)]
    x_restriction = Or([NotEquals(x[i], Int(0)) for i in range(o)])

    sub_var1_with_x0 = {vars1[i]: x0[i] for i in range(o)}
    sub_var2_with_x0 = {vars2[i]: x0[i] for i in range(o)}
    sub_var1_with_x  = {vars1[i]: x[i] for i in range(o)}
    sub_var2_with_x  = {vars2[i]: x[i] for i in range(o)}

    # ============================
    # Handle inequalities
    # ============================
    gamma = []

    for i, ineq in enumerate(ineqs):
        left, right = ineq.arg(0), ineq.arg(1)
        l_coeffs, l_const = collect_sum_terms(left)
        r_coeffs, r_const = collect_sum_terms(right)

        l_coeffs, r_coeffs, const = arithmetic_solver(l_coeffs, l_const, r_coeffs, r_const, set(vars1))

        left_x = reconstruct_from_coeff_map({sub_var1_with_x[v]: c for v, c in l_coeffs.items()}, 0)
        left_x0 = reconstruct_from_coeff_map({sub_var1_with_x0[v]: c for v, c in l_coeffs.items()}, 0)
        right_x0 = reconstruct_from_coeff_map({sub_var2_with_x0[v]: c for v, c in r_coeffs.items()}, const)
        right_x = reconstruct_from_coeff_map({sub_var2_with_x[v]: c for v, c in r_coeffs.items() if v in vars2}, 0)

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

        left_hand_eq: ExtendedFNode = equation.arg(0)
        right_hand_eq: ExtendedFNode = equation.arg(1)

        # Peel of mod
        left: ExtendedFNode
        right: ExtendedFNode
        mod: Optional[int] = None

        assert left_hand_eq == MOD_NODE_TYPE
        assert cast(ExtendedFNode, left_hand_eq.arg(1)).is_int_constant()

        mod = cast(ExtendedFNode, left_hand_eq.arg(1)).constant_value()
        left = left_hand_eq.arg(0)

        assert right_hand_eq == MOD_NODE_TYPE
        assert cast(ExtendedFNode, right_hand_eq.arg(1)).is_int_constant()
        assert mod == right_hand_eq.arg(1).constant_value() 

        mod = right_hand_eq.arg(1).constant_value()
        right = right_hand_eq.arg(0)

        left_coeff_map, right_constant = collect_sum_terms(left)
        right_coeff_map, left_constant = collect_sum_terms(right)

        l_coeffs, r_coeffs, const = arithmetic_solver(left_coeff_map, left_constant, right_coeff_map, right_constant, set(vars1))

        left_x = reconstruct_from_coeff_map({sub_var1_with_x[v]: c for v, c in l_coeffs.items()}, 0)
        left_x0 = reconstruct_from_coeff_map({sub_var1_with_x0[v]: c for v, c in l_coeffs.items()}, 0)
        right_x = reconstruct_from_coeff_map({sub_var2_with_x[v]: c for v, c in r_coeffs.items() if v in vars2}, 0)

        #v (x0 + x) + wz
        combined_r_coeffs: Dict[ExtendedFNode, int] = {}
        for v, c in r_coeffs.items():
            if v in vars2:
                # put both the x0- and the x-versions in the same map
                combined_r_coeffs[sub_var2_with_x0[v]] = c
                combined_r_coeffs[sub_var2_with_x[v]]  = c
            else:
                # keep all other vars unchanged
                combined_r_coeffs[v] = c
        right_x_x0 = reconstruct_from_coeff_map(combined_r_coeffs, const)

        # TODO: Add the not back on

        def negate_if(term):
            if is_negated:
                return Not(term)
            else:
                return term

        g1 = negate_if(Equals(Mod(left_x0, Int(mod)), Mod(right_x_x0, Int(mod))))# u x0 % e = v (x0 + x) + wz + d % e
        g2 = Equals(Mod(left_x, Int(mod)), Int(0))# u x % e = 0 % e
        g3 = Equals(Mod(right_x, Int(mod)), Int(0))# vx %e = 0 % e

        gamma.append(And(g1, g2, g3))

    # ============================
    # Handle equalities
    # ============================
    for i, eq in enumerate(eqs):

        # rx = sy + tz + h

        left, right = eq.arg(0), eq.arg(1)
        l_coeffs, l_const = collect_sum_terms(left)
        r_coeffs, r_const = collect_sum_terms(right)

        l_coeffs, r_coeffs, const = arithmetic_solver(l_coeffs, l_const, r_coeffs, r_const, set(vars1))

        left_x = reconstruct_from_coeff_map({sub_var1_with_x[v]: c for v, c in l_coeffs.items()}, 0) # rx
        right_x = reconstruct_from_coeff_map({sub_var2_with_x[v]: c for v, c in r_coeffs.items() if v in vars2}, 0) # vx

        left_x0 = reconstruct_from_coeff_map({sub_var1_with_x0[v]: c for v, c in l_coeffs.items()}, 0) # r x0
        right_x0 = reconstruct_from_coeff_map({sub_var2_with_x0[v]: c for v, c in r_coeffs.items()}, 0) # s x0 + tz + h

        gamma.append(And(
            Equals(left_x, Int(0)), # rx = 0
            Equals(right_x, Int(0)), # vx = 0
            Equals(left_x0, right_x0) # r x_0 = s x0 + tz + h
        ))

    # ============================
    # Step 8: Final assembly
    # ============================
    guarded_gamma = And([Or(Not(qs[i]), gamma[i]) for i in range(l + n + m)])

    result = And(x_restriction, prop_skeleton, admissible, guarded_gamma)

    return Exists(omega + qs, Exists(p + x + x0, result))
    

def full_ramsey_elimination_int(formula: ExtendedFNode):
    assert formula.is_ramsey()
    f = int_inequality_rewriter(formula) # Doesn't change formula size
    f = push_negations_inside(f) # Only introduces new terms for !=, so will produce a small formula

    # Will introduce a new two new terms(v_0 + w_1 and distinctness) and 4 atoms for every existentially quantified variable
    f = eliminate_integer_existential_quantifiers(f) 

    return eliminate_ramsey_int(f)




if __name__ == "__main__":
    from RamseyQuantors.environment import push_ramsey
    from RamseyQuantors.shortcuts import *

    push_ramsey()
    get_env().enable_infix_notation = True

    x = Symbol("a", INT)
    y = Symbol("b", INT)
    f =  And(LT(Times(Int(2), y), Plus(x, 1)), GT(Plus(x, 1), Int(5))) # And(Int(2)*y <= x, x >= Int(5))
    qf = Ramsey([x], [y], f)

    print(full_ramsey_elimination_int(qf).serialize())





