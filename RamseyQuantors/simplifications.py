from pysmt.operators import AND, EXISTS, FORALL, OR, EQUALS, PLUS, NOT, IMPLIES, IFF, TIMES, MINUS
import pysmt.operators as operators
from pysmt.shortcuts import GT, LE, And, ForAll, Or, LT, Exists, Times, Not, Int
from RamseyQuantors.fnode import ExtendedFNode
from typing import Tuple, Dict, Set
from RamseyQuantors.formula_utils import create_node, isAtom, apply_to_atoms
from RamseyQuantors.operators import MOD_NODE_TYPE

type SumOfTerms = Dict[ExtendedFNode, int]

def arithmetic_solver(left: SumOfTerms, left_const: int,
                      right:SumOfTerms, right_const: int,
                      vars: Set[ExtendedFNode]) -> Tuple[SumOfTerms, SumOfTerms, int]:
    """
    Solve an sum of products for a list of variables.
    Returns the left side only containing vars and their coefficients,
    and the right side with vars, coefficients and a constant integer part.
    """

    assert isinstance(vars, set) # Sets speed up the process alot so make sure we get a set

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
                        if left.arg(0).node_type() == MOD_NODE_TYPE or right.arg(0).node_type() == MOD_NODE_TYPE: # Ignore equations with mod
                            return Not(subformula)
                        else:
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

