from typing import Mapping, Tuple, Dict, Set, Union

from pysmt.operators import EQUALS, NOT
import pysmt.operators as operators
from pysmt.shortcuts import FALSE, GT,TRUE, And, ForAll, Or, LT, Exists, Not, Int, Plus

from ramsey_extensions.fnode import ExtendedFNode
from ramsey_extensions.operators import MOD_NODE_TYPE

from ramsey_elimination.formula_utils import create_node

type SumOfTerms = Mapping[ExtendedFNode, Union[int, float]]
type Numeric = Union[int, float]

def arithmetic_solver(
    left: SumOfTerms, left_const: Numeric,
    right: SumOfTerms, right_const: Numeric,
    vars: Set[ExtendedFNode]
) -> Tuple[SumOfTerms, SumOfTerms, Numeric]:
    """
    Solve a linear equation for a set of variables:
      left * x + left_const = right * x + right_const

    Returns:
      (new_left, new_right, const) such that
        new_left * x = new_right * x + const
    """
    assert isinstance(vars, set)

    # Split terms: keep vars on LHS, move others to RHS
    Lw, Lo = {}, {}
    for sym, coeff in left.items():
        if sym in vars:
            Lw[sym] = coeff
        else:
            Lo[sym] = -coeff

    Rw, Ro = {}, {}
    for sym, coeff in right.items():
        if sym in vars:
            Rw[sym] = -coeff
        else:
            Ro[sym] = coeff

    # Combine same-symbol terms on left
    new_left: SumOfTerms = {}
    for sym, coeff in Lw.items():
        new_left[sym] = coeff + Rw.pop(sym, 0)
    # any remaining Rw go on LHS
    new_left |= Rw

    # Combine non‐vars on right
    new_right: SumOfTerms = {}
    for sym, coeff in Ro.items():
        new_right[sym] = coeff + Lo.pop(sym, 0)
    new_right |= Lo

    # Constant shift
    const: Numeric = right_const - left_const

    return new_left, new_right, const

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
                    return And(make_int_input_format(a), Not(make_int_input_format(b)))
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
                case operators.BOOL_CONSTANT:
                    if sub.is_true():
                        return FALSE()
                    else:
                        return TRUE()
                case _:
                    print(f"Fall through case {node}")
                    return create_node(NOT, make_int_input_format(sub), node._content.payload)
        case operators.IMPLIES:
            return Or(make_int_input_format(Not(node.arg(0))), make_int_input_format(node.arg(1)))

        case operators.IFF:
            return And(
                Or(make_int_input_format(Not(node.arg(0))), make_int_input_format(node.arg(1))),
                Or(make_int_input_format(Not(node.arg(1))), make_int_input_format(node.arg(0)))
            )
        case _:
            return create_node(typ, tuple([make_int_input_format(c) for c in node.args()]), node._content.payload)

def apply_subst(coeffs: Mapping[ExtendedFNode, Union[int, float]], subst: Mapping[ExtendedFNode, ExtendedFNode]) -> Dict[ExtendedFNode, Union[int, float]]:
    """
    Apply a substitution map to a coefficient map, keeping unmapped keys.
    """
    return {subst.get(var, var): coeff for var, coeff in coeffs.items()}
