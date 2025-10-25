from typing import Mapping, Tuple, Set, Union

from pysmt.operators import EQUALS, NOT
import pysmt.operators as operators
from pysmt.shortcuts import FALSE, GT, TRUE, And, Equals, ForAll, Or, LT, Exists, Not, Int, Plus

from ramsey_extensions.fnode import ExtendedFNode

from ramsey_elimination.formula_utils import contains_mod, create_node

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

    If `vars` is empty, all symbols from left and right are treated as variables
    and moved to the left; the constant is placed on the right as before.
    """
    assert isinstance(vars, set)

    # If no vars provided, treat all symbols as vars (move them to the left)
    if len(vars) == 0:
        vars = set(left.keys()) | set(right.keys())

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

    # Constant shift (constant moved to the right)
    const: Numeric = right_const - left_const

    return new_left, new_right, const

def _make_input_format_logic(node: ExtendedFNode, is_int: bool) -> ExtendedFNode:
    """
    Pushes negations down to atoms and rewrites relations based on
    integer or real semantics.

    Args:
        node: The formula node to process.

    Returns:
        The transformed formula node.
    """
    # A direct recursive call is cleaner and captures the `is_int` context.
    def recurse(n):
        return _make_input_format_logic(n, is_int)

    typ = node.node_type()

    match typ:
        # 1. Top-level atom transformations (logic differs for int/real)
        case operators.LE if is_int:
            # For integers: x <= y  =>  x < y + 1
            lhs, rhs = node.args()
            return LT(lhs, Plus(rhs, Int(1)))

        case typ if typ in (operators.LT, operators.LE, EQUALS):
            # For reals, LE/LT/EQUALS are kept as is.
            # For integers, LT/EQUALS are also kept as is.
            return node

        # 2. Push negations inward
        case operators.NOT:
            sub = node.arg(0)
            t = sub.node_type()

            match t:
                # --- De Morgan's laws and other logical equivalences ---
                case operators.NOT:
                    return recurse(sub.arg(0))
                case operators.AND:
                    return Or([recurse(Not(c)) for c in sub.args()])
                case operators.OR:
                    return And([recurse(Not(c)) for c in sub.args()])
                case operators.IMPLIES:
                    a, b = sub.args()
                    return And(recurse(a), recurse(Not(b)))
                case operators.IFF:
                    a, b = sub.args()
                    return And(
                        Or(recurse(Not(a)), recurse(Not(b))),
                        Or(recurse(a), recurse(b))
                    )
                case operators.FORALL:
                    return Exists(sub.quantifier_vars(), recurse(Not(sub.arg(0))))
                case operators.EXISTS:
                    return ForAll(sub.quantifier_vars(), recurse(Not(sub.arg(0))))

                # --- Negated atoms (logic differs for int/real) ---
                case operators.LE:
                    # ~(x <= y) => x > y => y < x
                    lhs, rhs = sub.args()
                    return LT(rhs, lhs)
                case operators.LT:
                    # ~(x < y) => x >= y => y <= x
                    lhs, rhs = sub.args()
                    if is_int:
                        # For integers: y <= x  =>  y < x + 1
                        return LT(rhs, Plus(lhs, Int(1)))
                    else:
                        # !(x < y) => x >= y => x > y \/ x = y
                        return Or(LT(rhs, lhs), Equals(lhs, rhs))
                case operators.EQUALS:
                    lhs, rhs = sub.args()
                    if contains_mod(lhs) or contains_mod(rhs):
                        return Not(sub)
                    else:
                        # ~(x = y) => x < y or y < x
                        return Or(LT(lhs, rhs), GT(lhs, rhs))
                case operators.SYMBOL:
                    return Not(sub)
                case operators.BOOL_CONSTANT:
                    return FALSE() if sub.is_true() else TRUE()
                case _:
                    print(f"Fall through case {node}")
                    return create_node(NOT, recurse(sub), node._content.payload)

        # 3. Top-level logical connective transformations
        case operators.IMPLIES:
            # a => b  =>  ~a or b
            return Or(recurse(Not(node.arg(0))), recurse(node.arg(1)))

        case operators.IFF:
            # a <=> b  =>  (~a or b) and (~b or a)
            a, b = node.args()
            return And(
                Or(recurse(Not(a)), recurse(b)),
                Or(recurse(Not(b)), recurse(a))
            )
        # 4. Default case: recurse on children
        case _:
            return create_node(typ, tuple([recurse(c) for c in node.args()]), node._content.payload)


def make_int_input_format(node: ExtendedFNode) -> ExtendedFNode:
    """
    Push negations down to atoms for integer arithmetic.
    Rewrite integer <= into < with +1.
    """
    return _make_input_format_logic(node, is_int=True)


def make_real_input_format(node: ExtendedFNode) -> ExtendedFNode:
    """
    Push negations down to atoms for real arithmetic.
    """
    return _make_input_format_logic(node, is_int=False)

