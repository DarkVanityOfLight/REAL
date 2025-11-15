from typing import Callable, Mapping, Tuple, Set, Union
from warnings import warn_explicit

import pysmt.operators as op
from pysmt.shortcuts import FALSE, GT, LE, TRUE, And, Equals, ForAll, Or, LT, Exists, Not, Int, Plus

from ramsey_extensions.fnode import ExtendedFNode

from ramsey_elimination.formula_utils import contains_mod, create_node, is_atom

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

# ---- Atom rewrite strategies ----
def integer_atom_rewrite(node: ExtendedFNode) -> ExtendedFNode:
    t = node.node_type()
    if t == op.LE:
        lhs, rhs = node.args()
        return LT(lhs, Plus(rhs, Int(1)))
    return node


def identity_atom_rewrite(node: ExtendedFNode) -> ExtendedFNode:
    return node

def mixed_atom_rewrite(node: ExtendedFNode) -> ExtendedFNode:
    if node.is_le():
        return Or(Equals(node.arg(0), node.arg(1)), LT(node.arg(0), node.arg(1)))
    return node


def make_input_format(
    node: ExtendedFNode,
    atom_rewrite: Callable[[ExtendedFNode], ExtendedFNode]
) -> ExtendedFNode:
    """
    Single-pass recursion: push negations and apply atom rewrite.
    """
    def rec(n: ExtendedFNode, negated: bool = False) -> ExtendedFNode:
        t = n.node_type()

        # --- Handle boolean constants directly ---
        if t == op.BOOL_CONSTANT:
            return FALSE() if (negated ^ n.is_true()) else TRUE()

        # --- Negation pushdown: flip the flag ---
        if t == op.NOT:
            return rec(n.arg(0), not negated)

        # --- Connectives ---
        if t in (op.AND, op.OR):
            if negated:
                # Apply De Morgan
                ctor = Or if t == op.OR else And
            else:
                ctor = And if t == op.AND else Or
            return ctor([rec(c, negated) for c in n.args()])

        if t == op.IMPLIES:
            a, b = n.args()
            # a => b = ~a or b
            return rec(Or(Not(a), b), negated)

        if t == op.IFF:
            a, b = n.args()
            # a <=> b = (a => b) & (b => a)
            return rec(And(Or(Not(a), b), Or(Not(b), a)), negated)

        if t == op.FORALL:
            if negated:
                return Exists(n.quantifier_vars(), rec(n.arg(0), True))
            else:
                return ForAll(n.quantifier_vars(), rec(n.arg(0), False))
        if t == op.EXISTS:
            if negated:
                return ForAll(n.quantifier_vars(), rec(n.arg(0), True))
            else:
                return Exists(n.quantifier_vars(), rec(n.arg(0), False))

        # --- Atomic formulas ---
        if is_atom(n):
            n_new = n
            if negated:
                # Apply negation to atom
                lhs, rhs = (n.args() + (None,))[:2]
                match t:
                    case op.LE:
                        n_new = LT(rhs, lhs)
                    case op.LT:
                        n_new = LE(rhs, lhs)
                    case op.EQUALS:
                        if contains_mod(lhs) or contains_mod(rhs):
                            n_new = Not(n)
                        else:
                            n_new = Or(LT(lhs, rhs), GT(lhs, rhs))
                    case op.SYMBOL:
                        n_new = Not(n)
            return atom_rewrite(n_new)

        # --- Recurse for other composite nodes ---
        if not n.is_ramsey():
            from logging import warning
            warning(f"Unknown node type when walking tree: {n}")
        rewritten_children = tuple(rec(c, False) for c in n.args())
        return create_node(t, rewritten_children, n._content.payload)

    return rec(node)


# ---- Convenience wrappers ----
def make_int_input_format(node: ExtendedFNode) -> ExtendedFNode:
    return make_input_format(node, integer_atom_rewrite)


def make_real_input_format(node: ExtendedFNode) -> ExtendedFNode:
    return make_input_format(node, identity_atom_rewrite)

def make_mixed_input_format(node: ExtendedFNode) -> ExtendedFNode:
    return make_input_format(node, mixed_atom_rewrite)
