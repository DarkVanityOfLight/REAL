from pysmt.operators import AND, EXISTS, FORALL, OR, EQUALS, PLUS, NOT, IMPLIES, IFF, TIMES, MINUS
import pysmt.operators as operators
from pysmt.shortcuts import GT, LE, And, ForAll, Or, LT, Exists, Times, Not, Int, Plus
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
            Lo[k] = -v # Is moved to the other side so substracted

    Rw, Ro = {}, {}
    for k, v in right.items():
        if k in vars:
            Rw[k] = -v # Is moved to the other side so substracted
        else:
            Ro[k] = v

    # Move all variables with vars to the left
    new_left = {}
    for k, v in Lw.items():
        new_left[k] = v + Rw.pop(k, 0)

    new_left = new_left | Rw

    # Move all variables without vars to the right
    new_right = {}
    for k, v in Ro.items():
        new_right[k] = v + Lo.pop(k, 0)

    new_right = new_right | Lo

    const = right_const - left_const

    return (new_left, new_right, const)

def contains_mod(node: ExtendedFNode) -> bool:
    """Check if a node contains a modulo operation anywhere in its subtree."""
    if node.node_type() == MOD_NODE_TYPE:
        return True
    for arg in node.args():
        if contains_mod(arg):
            return True
    return False

def make_int_input_format(node: ExtendedFNode) -> ExtendedFNode:
    """
    Push negations down to atoms
    Rewrite integer <= into < with +1
    """
    typ = node.node_type()
    match typ:
        case operators.LE:
            # x <= y => x < y+1
            lhs, rhs = node.args()

            return LT(lhs, Plus(rhs, Int(1)))

        case typ if typ in (operators.LT, EQUALS):
            return node

        # Push inside
        case operators.NOT:
            sub = node.arg(0)
            t = sub.node_type()

            match t:
                case operators.NOT:
                    return make_int_input_format(sub.arg(0))
                case operators.AND:
                    return Or([make_int_input_format(Not(c)) for c in sub.args()])
                case operators.OR:
                    return And([make_int_input_format(Not(c)) for c in sub.args()])
                case operators.IMPLIES:
                    a, b = sub.args()
                    return And(make_int_input_format(a), make_int_input_format(Not(b)))
                case operators.IFF:
                    a, b = sub.args()
                    return And(
                        Or(make_int_input_format(Not(a)), make_int_input_format(Not(b))),
                        Or(make_int_input_format(a), make_int_input_format(b))
                    )
                case operators.FORALL:
                    vars = sub.quantifier_vars()
                    body = sub.arg(0)
                    return Exists(vars, make_int_input_format(Not(body)))
                case operators.EXISTS:
                    vars = sub.quantifier_vars()
                    body = sub.arg(0)
                    return ForAll(vars, make_int_input_format(Not(body)))

                # Negated atoms
                case operators.LE:
                    # ~(x <= y) => x > y => y < x
                    lhs, rhs = sub.args()
                    return LT(rhs, lhs)
                case operators.LT:
                    lhs, rhs = sub.args()
                    return LT(rhs, Plus(lhs, Int(1)))
                case operators.EQUALS:
                    lhs, rhs = sub.args()
                    if contains_mod(lhs) or contains_mod(rhs):
                        return Not(sub)
                    else:
                        # ~ (x = y) => x < y \/ y < x
                        return Or(LT(lhs, rhs), GT(lhs, rhs))
                case operators.SYMBOL:
                    return Not(sub)
                case _:
                    print(f"Fall through case {node}")
                    return create_node(NOT, make_int_input_format(sub), node._content.payload)

        case _:
            return create_node(typ, tuple([make_int_input_format(c) for c in node.args()]), node._content.payload)

def apply_subst(coeffs: Dict[ExtendedFNode, int], subst: Dict[ExtendedFNode, ExtendedFNode]) -> Dict[ExtendedFNode, int]:
    """
    Apply a substitution map to a coefficient map, keeping unmapped keys.
    """
    return {subst.get(var, var): coeff for var, coeff in coeffs.items()}
