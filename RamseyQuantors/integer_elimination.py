from pysmt.fnode import FNode
from pysmt.operators import EQUALS
from pysmt.shortcuts import LE, LT, And, Equals, Exists, Int, Not, NotEquals, Or, Symbol, Plus, GE
from pysmt.typing import INT
from RamseyQuantors.fnode import ExtendedFNode
from RamseyQuantors.operators import MOD_NODE_TYPE, RAMSEY_NODE_TYPE

from typing import Dict, Tuple, cast

from RamseyQuantors.shortcuts import Mod, Ramsey
from RamseyQuantors.simplifications import int_inequality_rewriter, push_negations_inside, solve_for

from RamseyQuantors.formula_utils import collect_atoms, collect_subterms_of_var, restrict_to_bool, split_left_right



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
    x : Tuple[FNode, ...] = formula._content.payload[0]
    y : Tuple[FNode, ...] = formula._content.payload[1]

    # Add the newly introduced variables
    new_x =  x + v1 + v2
    new_y = y + w1 + w2

    #Ensure pairwise distinct subclique
    pairwise_distinct = Or([Or(x[i] < y[i], y[i] < x[i]) for i in range(len(x))])

    # Create a new Ramsey quantifier now with the substituted formula, the pairwise distinctnes and the two new vectors of bound variables
    return Ramsey(new_x, new_y, And(substituted_formula, pairwise_distinct))


def eliminate_ramsey_int(qformula: ExtendedFNode) -> ExtendedFNode:
    """
    Take in a formula of the for (ramsey x y phi), assuming that phi is quantifier free and w-simple
    Return an equivalent formula without the ramsey quantifier
    """
    assert qformula.node_type() == RAMSEY_NODE_TYPE

    formula = qformula.arg(0)

    # TODO: Merge this with collecting the atoms
    formula = solve_for(formula, qformula.quantifier_vars()[0]).simplify()

    eqs, ineqs = collect_atoms(cast(ExtendedFNode, formula))
    n, m = len(eqs), len(ineqs)

    # Introduce new symbols to guess which atoms should be satisfied
    qs = [Symbol(f"q_{i}", INT) for i in range(len(eqs) + len(ineqs))]
    q_restriction = restrict_to_bool(qs)

    # Build the propositional skeleton by substituting all atoms with their corresponding q
    prop_skeleton = formula.substitute({atom: Equals(qs[i], Int(1)) for i, atom in enumerate(eqs + ineqs)})

    # Define the limits for each term in the atoms(aka. the profile of the clique)
    p, omega = [], []
    for i in range(2*m):
        p.append(Symbol(f"p_{i}", INT))
        omega.append(Symbol(f"o_{i}", INT))

    omega_restriction = restrict_to_bool(omega)

    # Ensure the profile is admissible that is either 
    # p[2i] < p[2i+1]  or omega[2i+1] = 1
    # The upper lower bound is smaller then the upper on the atom
    # The upper bound is infinite
    admissible = And([Or(And(Equals(omega[2*i], Int(0)), LT(p[2*i], p[2*i+1])), Equals(omega[2*i+1], Int(1))) for i in range(m)])


    # Create symbols for the arithmetic series (x_0 + k x) that contains the clique
    vars1, vars2 = qformula.quantifier_vars()

    o = len(vars1)

    x0, x = [], []
    for i in range(o):
        x0.append(Symbol(f"x0_{i}", INT))
        x.append(Symbol(f"x{i}", INT))

    # Restrict x != 0 
    x_restriction = Or([NotEquals(x[i], Int(0)) for i in range(o)])

    # Prepare subsitution maps
    sub_var1_with_x0 = {}
    sub_var2_with_x0 = {}
    sub_var1_with_x = {}
    sub_var2_with_x = {}
    
    for i in range(o):
        sub_var1_with_x0[vars1[i]] = x0[i]
        sub_var2_with_x0[vars2[i]] = x0[i]

        sub_var1_with_x[vars1[i]] = x[i]
        sub_var2_with_x[vars2[i]] = x[i]


    # Construct gamma
    gamma = []
    for i, ineq in enumerate(ineqs):

        # r x < s y + t z + h

        # Check wich side contains our first variable vector
        left, right = ineq.arg(0), ineq.arg(1)

        terms_with_vars2, _ = collect_subterms_of_var(right, vars2)

        # TODO: Pull out substitutions, (since the terms are small this will probs not make a huge difference)
        g1 = Or(Equals(omega[2*i], Int(1)), And(LE(left.substitute(sub_var1_with_x0), p[2*i]), LE(left.substitute(sub_var1_with_x), Int(0))))
        g2 = Or(Equals(omega[2*i+1], Int(1)), 
                And(
                    LE(p[2*i+1], right.substitute(sub_var2_with_x0)),
                    GE(terms_with_vars2.substitute(sub_var1_with_x), Int(0))
                )
            )
        g3 = Or(Equals(omega[2*i+1], Int(0)),
                LT(Int(0), terms_with_vars2.substitute(sub_var2_with_x))
                )

        gamma.append(And(g1, g2, g3))


    # TODO: Handle equality without mods directly
    sub_var2_with_sum = {vars2[i] : Plus(x0[i], x[i]) for i in range(o)}
    for i, eq in enumerate(eqs):
        assert eq.node_type() == EQUALS
        assert eq.arg(0).node_type() == MOD_NODE_TYPE

        left, right = split_left_right(eq, vars1)

        # spliting assures that left is the left hand side in the equation below
        #eq: u*vars1 % e == v*vars2 + wz + d % e

        # u x0 % e == v (x0 + x) + wz + d % e
        g1 = eq.substitute(sub_var1_with_x0 | sub_var2_with_sum)

        # ux % e = 0
        g2 = Equals(left.substitute(sub_var1_with_x), 0)

        # vx % e = 0
        vx : FNode = Plus(collect_subterms_of_var(right, vars2)[0])
        mod_div = eq.arg(0).arg(1)
        g3 = Equals(Mod(vx.substitute(sub_var2_with_x), mod_div), 0)

        gamma.append(And(g1, g2, g3))


    restrictions = And(q_restriction, x_restriction, omega_restriction)
    result = And(restrictions, prop_skeleton, admissible)
    result =  And(result, And([Or(Not(Equals(qs[i], Int(1))), gamma[i]) for i in range(n+m)]))

    return Exists(qs+p+omega+x+x0, result)
    

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





