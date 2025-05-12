from pysmt.fnode import FNode
from pysmt.operators import AND, EXISTS, FORALL, OR, EQUALS, PLUS, NOT, IMPLIES, IFF, TIMES, MINUS
import pysmt.operators as operators
from pysmt.shortcuts import GT, LE, And, ForAll, Or, LT, Minus, Exists, Plus, Times, Not, Int
from RamseyQuantors.fnode import ExtendedFNode
from typing import Iterable, Tuple, cast, Dict, Set
from RamseyQuantors.formula_utils import create_node, subterm, isAtom, apply_to_atoms

type SumOfTerms = Dict[ExtendedFNode, int]

def arithmetic_solver(left: SumOfTerms, left_const: int,
                      right:SumOfTerms, right_const: int,
                      vars: Set[ExtendedFNode]) -> Tuple[SumOfTerms, SumOfTerms, int]:
    """
    Solve an sum of products for a list of variables.
    Returns the left side only containing vars and their coefficients,
    and the right side with vars, coefficients and a constant integer part.
    """

    Lw, Lo = {}, {}
    for k, v in left.items():
        if k in vars:
            Lw[k] = v
        else:
            Lo[k] = v

    Rw, Ro = {}, {}
    for k, v in right.items():
        if k in vars:
            Lw[k] = v
        else:
            Lo[k] = v

    # Move all variables with vars to the left
    new_left = {}
    for k, v in Lw.items():
        new_left[k] = v - Rw.pop(k, 0)

    new_left = new_left | Rw

    # Move all variables without vars to the right
    new_right = {}
    for k, v in Ro.items():
        new_right[k] = v - Lo.pop(k, 0)

    new_right = new_right | Lo

    const = right_const - left_const

    return (new_left, new_right, const)

def solve_for(f: FNode, vars: Iterable[FNode]) -> FNode:
    """
    Solve formula f such that all variables in 'vars' are moved to the left side of the (in)equality.
    Assumes the formula is already a sum of products.
    """

    # FIXME: will probably die on mod
    def solve(atom: ExtendedFNode):
        # Determine the original operator
        op = atom.node_type()
        left, right = atom.arg(0), atom.arg(1)

        # Split left into variable terms (Lw) and non-variable terms (Lo)
        Lw = subterm(left, vars, True)
        Lo = subterm(left, vars, False)

        # Split right into variable terms (Rw) and non-variable terms (Ro)
        Rw = subterm(right, vars, True)
        Ro = subterm(right, vars, False)

        # Compute new_left and new_right
        new_left = arithmetic_simplifier(Minus(Lw, Rw))
        new_right = arithmetic_simplifier(Minus(Ro, Lo))

        # Create the new atom with the original operator
        new_atom = create_node(op, (new_left, new_right))

        return new_atom.simplify()

    return apply_to_atoms(cast(ExtendedFNode, f), solve)



def collect_sum_terms(
    term: ExtendedFNode
) -> Tuple[Dict[ExtendedFNode, int], int]:
    """
    Flattens a sum/difference tree and returns:
      - coefficients: a dict mapping each non-constant subterm to its net integer coefficient
      - constant_term: the sum of all standalone integer literals

    Example:
      collect_sum_terms( 5*x - 3*a + 7 )  ==>  ({x:5, a:-3}, 7)
    """

    coefficients: Dict[ExtendedFNode, int] = {}
    constant_term = 0

    def _add_term(core: ExtendedFNode, coeff: int):
        nonlocal constant_term
        # If it's a pure integer literal, fold into constant_term
        if core.is_int_constant():
            constant_term += coeff * core.constant_value()
        else:
            # Otherwise accumulate into the dict
            coefficients[core] = coefficients.get(core, 0) + coeff

    def recurse(node: ExtendedFNode, sign: int):
        """sign is +1 or -1 depending on whether we're under a MINUS."""
        nt = node.node_type()

        if nt == PLUS:
            for c in node.args():
                recurse(c, sign)

        elif nt == MINUS:
            a, b = node.args()
            recurse(a, sign)      # + a
            recurse(b, -sign)     # - b

        else:
            # Leaf summand: maybe a product with an int coeff
            coeff, rest_factors = 1, []  # we'll pull out any integer literal
            if nt == TIMES:
                for arg in node.args():
                    if arg.is_int_constant():
                        coeff *= arg.constant_value()
                    else:
                        rest_factors.append(arg)
            else:
                rest_factors = [node]

            # If there were multiple non-const factors, re-make a TIMES; else take the single factor.
            if len(rest_factors) == 0:
                # pure constant times => just treat via _add_term
                _add_term(Int(1), sign * coeff)
            elif len(rest_factors) == 1:
                core = rest_factors[0]
                _add_term(core, sign * coeff)
            else:
                core = Times(rest_factors)
                _add_term(core, sign * coeff)

    recurse(term, 1)
    return coefficients, constant_term

        
def arithmetic_simplifier(term: ExtendedFNode) -> ExtendedFNode:
    """ Simplifies sums of terms, eg. a - b - a => -b """
    terms, constant = collect_sum_terms(term)
    filtered_terms = filter(lambda item: item[1] != 0, terms.items())

    return Plus([Times(Int(coeff), var) for var, coeff in filtered_terms] + [Int(constant)])


def int_inequality_rewriter(formula: ExtendedFNode) -> ExtendedFNode:
    """
    Rewrite x <= y to x < y +1, this equivalenz only holds for the integer case.
    """

    def inequality_maker(atom: ExtendedFNode):
        # We only actually eliminate >=
        if atom.node_type() == operators.LE:
            return LT(atom.arg(0), (atom.arg(1) + 1))
        else:
            return atom

    return apply_to_atoms(formula, inequality_maker)



def push_negations_inside(formula: ExtendedFNode) -> ExtendedFNode:
    """Takes in a formula,
    and returns an equivalent formula with all negations pushed down onto the atoms.
    """

    if isAtom(formula):
        return formula
    
    match formula.node_type():
        case op if op == NOT:
            subformula = formula.arg(0)

            if isAtom(subformula):
                left, right = subformula.args()
                match subformula.node_type():
                    case op if op == operators.LE:
                        # ~(x <= y) => y < x
                        return LT(right, left)
                    case op if op == operators.LT:
                        # ~(x < y) => y <= x
                        return LE(right, left)
                    case op if op == EQUALS:
                        # ~ (x = y) => x < y \/ y < x
                        return Or(LT(left, right), GT(left, right))

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
                case op if op == FORALL:
                    return Exists(subformula.quantifier_vars, Not(subformula.arg(0)))
                case op if op == EXISTS:
                    return ForAll(subformula.quantifier_vars, Not(subformula.arg(0)))
            raise Exception(f"Unsupported node type {formula.node_type()}")

        case _:
            args = tuple(push_negations_inside(arg) for arg in formula.args())
            return create_node(formula.node_type(), args, formula._content.payload) 

