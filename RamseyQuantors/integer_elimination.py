from pysmt import operators
from pysmt.fnode import IRA_OPERATORS, FNode
from pysmt.operators import AND, EQUALS, IFF, IMPLIES, OR, NOT, PLUS, SYMBOL, TIMES
from pysmt.shortcuts import FALSE, LE, LT, And, Equals, Exists, Int, Not, NotEquals, Or, Symbol, Plus, GE
from pysmt.typing import BOOL, INT
from RamseyQuantors.fnode import ExtendedFNode
from RamseyQuantors.operators import MOD_NODE_TYPE, RAMSEY_NODE_TYPE

from typing import Dict, Optional, Tuple, cast, List, Iterable, Set

from RamseyQuantors.shortcuts import Mod, Ramsey



# ============= Utils =============
def isAtom(atom: FNode) -> bool:
    """
    Check if the given node is an atom, that is an equation of the form
    ... ~ ... with ~ in { =, <, > }
    """
    return atom.get_type() == BOOL and (atom.node_type() in operators.IRA_RELATIONS or atom.node_type() == operators.EQUALS)

# TODO: Find a good way to merge with the initial simplification
def collect_atoms(formula: ExtendedFNode) -> Tuple[Tuple[ExtendedFNode, ...], Tuple[ExtendedFNode, ExtendedFNode]]:
    """Collect all atoms, as (inequalities, equalities)"""
    eqs = []
    ineqs = []

    stack = [formula]
    while stack:
        subformula = stack.pop()
        match subformula.node_type():
            case op if op in {AND, OR, IFF, IMPLIES, NOT}:
                for arg in subformula.args():
                    stack.append(arg)
            case op if op == EQUALS:
                eqs.append(subformula)
            case op if op == operators.LT:
                ineqs.append(subformula)
            case _:
                print(f"Did not handle {subformula} when collecting atoms.")

    return tuple(eqs), tuple(ineqs)
    
def restrict_to_bool(values: List[FNode]):
    """Given a list of symbols, return a formula that restricts them to integer 0 or 1"""
    return And([Or(Equals(v, Int(1)), Equals(v, Int(0))) for v in values])

def split_left_right(atom: FNode, vars1: Iterable[FNode]) -> Tuple[FNode, FNode]:
    """
    Return (side_with_vars1, side_without).  Raise if vars1 is on both or neither side.
    """
    assert isAtom(atom)
    vars1 = set(vars1)
    left, right = atom.arg(0), atom.arg(1)

    # helper to collect all symbol-nodes in a subtree
    def collect_vars(node: FNode, acc: Set[FNode]):
        if node.node_type() == SYMBOL:
            acc.add(node)
        elif node.node_type() in IRA_OPERATORS or node.node_type() == MOD_NODE_TYPE:
            for c in node.args():
                collect_vars(c, acc)
        # else: constants/literals etc.

    left_syms, right_syms = set(), set()
    collect_vars(left, left_syms)
    collect_vars(right, right_syms)

    left_hits  = left_syms  & vars1
    right_hits = right_syms & vars1

    if left_hits and not right_hits:
        return left, right
    if right_hits and not left_hits:
        return right, left

    # no hits or ambiguous
    raise Exception(
        f"vars1={sorted(vars1)} found on both sides "
        f"({sorted(left_hits)} | {sorted(right_hits)}) "
        f"for atom: {atom}"
    )


def collect_subterms_of_var(term: FNode, vars: Iterable[FNode]) -> Optional[FNode]:
    """From a normal form term collect all coefficients of variables vars"""

    terms = []

    stack : List[FNode] = [term]
    while stack:
        node : FNode = stack.pop()

        match node.node_type():
            case op if op == PLUS:
                for sub in node.args():
                    stack.append(sub)

            case op if op == TIMES:
                if any([t in vars for t in node.args()]):
                    terms.append(node)

    return Plus(terms) if len(terms) > 0 else None


def push_negations_inside(qformula: FNode):
    """Takes in a quantifier free formula,
    and returns an equivalent formula with all negations pushed down onto the atoms
    """
    if isAtom(qformula):
        return qformula
    
    match qformula.node_type():
        case op if op == AND:
           return And([push_negations_inside(subformula) for subformula in qformula.args()]) 
        case op if op == OR:
           return And([push_negations_inside(subformula) for subformula in qformula.args()]) 
        case op if op == NOT:
            subformula = qformula.arg(0)

            if isAtom(subformula):
                return Not(subformula)

            match subformula.node_type():
                case op if op == NOT:
                    return push_negations_inside(subformula)
                case op if op == AND:
                    return Or([push_negations_inside(Not(child)) for child in subformula.args()])
                case op if op == OR:
                    return And([push_negations_inside(Not(child)) for child in subformula.args()])
                case op if op == IMPLIES:
                    # ~(a -> b) <=> ~(~ a \/ b) <=> a /\ ~ b
                    return And(push_negations_inside(subformula.arg(0)), push_negations_inside(Not(subformula.arg(1))))
                case op if op == IFF:
                    # ~(a <-> b) <=> (~a \/ ~b) /\ (a \/ b)
                    return And(
                            Or(push_negations_inside(Not(subformula.arg(0))), push_negations_inside(Not(subformula.arg(1)))),
                            Or(push_negations_inside(subformula.args(0)), push_negations_inside(subformula.args(1))))



# ============= Elimination =============

def make_as_inequality(formula: ExtendedFNode) -> ExtendedFNode:
    """
    Take in a formula of the form term ~ term with ~ in {<, >, <=, >=, =} 
    or (term) % e = (term) % e

    Return an equivalent formula using only <, > and term %e = term %e
    """

    match formula.node_type():
        # If we have a logical connective pass it through
        case op if op == AND:
           return And([make_as_inequality(cast(ExtendedFNode, subformula)) for subformula in formula.args()])
        case op if op == OR:
           return Or([make_as_inequality(cast(ExtendedFNode, subformula)) for subformula in formula.args()])
        case op if op == NOT:
            return Not(make_as_inequality(formula.arg(0)))

        # If we have equality or non strict inequalities, eliminate
        case op if op == EQUALS: # != is eliminated when parsing
            if any([subformula.node_type() == MOD_NODE_TYPE for subformula in formula.args()]): return formula

            # a = b <==>
            # a <= b => a < b+1
            # b <= a => b < a + 1
            return And(formula.arg(0) < (formula.arg(1) + 1), formula.arg(1) < (formula.arg(0) + 1))

        case op if op == operators.LE: # GE is eliminated when parsing
            return formula.arg(0) < (formula.arg(1) + 1)

        case op if op == operators.EXISTS:
            return Exists(formula.quantifier_vars(), make_as_inequality(formula.arg(0)))
        case op if op == RAMSEY_NODE_TYPE:
            vv1, vv2 = formula.quantifier_vars()
            return Ramsey(vv1, vv2, make_as_inequality(formula.arg(0)))

    return formula

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

    # TODO: What should happen if an atom appears twice
    eqs, ineqs = collect_atoms(formula)
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
    admissible = And([Or(And(Equals(omega[2*i], Int(0)), LT(p[2*i], p[2*i+1])), Equals(omega[2*i+1], Int(1))) for i in range(n)])


    # Create symbols for the arithmetic series (x_0 + k x) that contains the clique
    vars1, vars2 = qformula._content.payload

    o = len(vars1)

    x0, x = [], []
    for i in range(1):
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
        # Check wich side contains our first variable vector
        left, right = split_left_right(ineq, vars1)

        terms_with_vars2 = collect_subterms_of_var(right, vars2)

        g1 = Or(Equals(omega[2*i], Int(1)), And(LE(left.substitute(sub_var1_with_x0), p[2*i]), LE(left.substitute(sub_var1_with_x), Int(0))))
        g2 = Or(Equals(omega[2*i+1], Int(1)), 
                And(
                    LE(p[2*i+1], right.substitute(sub_var2_with_x0)),
                    GE(terms_with_vars2.substitute(sub_var1_with_x), Int(0)) if terms_with_vars2 else FALSE()
                )
            )
        g3 = Or(Equals(omega[2*i+1], Int(0)),
                LT(Int(0), terms_with_vars2.substitute(sub_var2_with_x)) if terms_with_vars2 else FALSE()
                )

        gamma.append(And(g1, g2, g3))


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
        vx : FNode = Plus(collect_subterms_of_var(right, vars2))
        mod_div = eq.arg(0).arg(1)
        g3 = Equals(Mod(vx.substitute(sub_var2_with_x), mod_div), 0)

        gamma.append(And(g1, g2, g3))


    restrictions = And(q_restriction, x_restriction, omega_restriction)
    result = And(restrictions, prop_skeleton, admissible)
    result =  And(result, And([Or(Not(Equals(qs[i], Int(1))), gamma[i]) for i in range(n+m)]))

    return Exists(qs+p+omega, result)
    

if __name__ == "__main__":
    from RamseyQuantors.environment import push_ramsey
    from RamseyQuantors.shortcuts import *

    push_ramsey()
    get_env().enable_infix_notation = True

    x = Symbol("a", INT)
    y = Symbol("b", INT)
    f = And(Int(2)*y <= x, x >= Int(5))
    print(f)
    inp = make_as_inequality(f)
    print(inp)
    qf = Ramsey([x], [y], inp)
    print(qf)


    print(eliminate_ramsey_int(qf).serialize())




