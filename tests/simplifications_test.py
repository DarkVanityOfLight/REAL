
import pytest
from pysmt.shortcuts import Int, Symbol, And, Or, ForAll, Exists, Equals, LT, LE, GT, Implies, Iff, Not, Times, Plus
from pysmt.typing import INT
import pysmt.operators as operators

from RamseyQuantors.formula_utils import isAtom, apply_to_atoms, create_node
from RamseyQuantors.simplifications import (
    arithmetic_solver,
    int_inequality_rewriter,
    push_negations_inside
)

# Define some integer symbols for tests
a = Symbol('a', INT)
b = Symbol('b', INT)
x = Symbol('x', INT)
y = Symbol('y', INT)
z = Symbol('z', INT)

# -- Helper function for comparing coefficient maps
def _map_eq(m1, m2):
    return all(m1.get(k, 0) == v for k, v in m2.items()) and all(m2.get(k, 0) == v for k, v in m1.items())

# --- Tests for arithmetic_solver ---

def test_arithmetic_solver_simple():
    # left: 5*x + 2*a , right: 3*x + 7*b , vars = {x}
    left = {x: 5, a: 2}
    right = {x: 3, b: 7}
    left_const = 4
    right_const = 10
    new_left, new_right, const = arithmetic_solver(left, left_const, right, right_const, {x})
    print(new_left)
    # x-coefficient: 5 - 3 = 2
    assert new_left == {x: 2}
    # non-vars: a and b on right: b:7, a:-2
    assert _map_eq(new_right, {a: -2, b: 7})
    # constant part: right_const - left_const
    assert const == 6

# --- Tests for int_inequality_rewriter ---

def test_int_inequality_rewriter_le():
    f = LE(x, y)
    g = int_inequality_rewriter(f)
    # Should rewrite x <= y  to x < y + 1
    assert g.node_type() == operators.LT
    left_arg, right_arg = g.args()
    assert left_arg == x
    # y + 1 appears on right
    assert right_arg.is_plus()
    terms = set(right_arg.args())
    assert y in terms and Int(1) in terms


def test_int_inequality_rewriter_mixed():
    f = And(LE(a, b), GT(x, y))
    g = int_inequality_rewriter(f)
    # GT is flipped, LE rewritten
    assert g.arg(0).arg(0) == a and g.arg(0).arg(1) == Plus(b, Int(1))
    assert g.arg(1).arg(0) == y and g.arg(1).arg(1) == x

# --- Tests for push_negations_inside ---

def test_push_negations_inside_atomic():
    # Atomic negation stays
    eq = Equals(x, y)
    neg = Not(eq)
    out = push_negations_inside(neg)
    # Should expand to x<y \/ y<x
    assert out.node_type() == operators.OR
    clauses = set(out.args())
    assert LT(x, y) in clauses and GT(x, y) in clauses


def test_push_negations_inside_composite():
    # ~(a /\ b) => ~a \/ ~b => push to atoms
    f = And(LT(x, y), LE(a, b))
    nf = push_negations_inside(Not(f))
    # Should be Or of (y <= x) and b > a
    assert nf.node_type() == operators.OR
    atoms = list(nf.args())
    # First: Not(LT(x,y)) -> y <= x
    assert atoms[0].node_type() == operators.LE and atoms[0].args() == (y, x)
    # Second: Not(LE(a,b)) -> b < a
    assert atoms[1] == LT(b, a)


def test_push_negations_inside_quantifiers():
    forall = ForAll([x], And(LT(x, y), Equals(a, b)))
    # ~(forall x. ...) -> exists x. ~(...)
    out = push_negations_inside(Not(forall))
    assert out.node_type() == operators.EXISTS
    # Inside, should have And around negated atoms
    inner = out.arg(0)
    print(inner)
    assert inner.node_type() == operators.OR or inner.node_type() == operators.AND

    exists = Exists([y], LT(x, y))
    # ~(exists y. x<y) -> forall y. ~(x<y) -> forall y. y <= x
    out2 = push_negations_inside(Not(exists))
    assert out2.node_type() == operators.FORALL
    body = out2.arg(0)
    assert body.node_type() == operators.LE and body.args() == (y, x)


def test_push_negations_inside_imp_iff():
    imp = Implies(LT(x, y), LT(y, z))
    # ~(P->Q) -> P /\ ~Q
    out = push_negations_inside(Not(imp))
    assert out.node_type() == operators.AND
    left, right = out.args()
    assert left == LT(x, y)
    assert right.node_type() == operators.LE and right.args() == (z, y)

    iff = Iff(LT(a, b), LT(b, a))
    # ~(P<->Q) -> (~P \/ ~Q) /\ (P \/ Q)
    out2 = push_negations_inside(Not(iff))
    assert out2.node_type() == operators.AND
    # Should have two Ors
    ors = [c for c in out2.args() if c.node_type() == operators.OR]
    assert len(ors) == 2

# --- Tests for isAtom and apply_to_atoms on mixed formulas ---

def test_apply_to_atoms_ignores_non_atoms():
    # Arithmetic term is not treated as atom
    term = Plus(x, y)
    out = apply_to_atoms(term, lambda atm: Int(99))
    # Plus stays unchanged
    assert out.node_type() == operators.PLUS and set(out.args()) == {x, y}


def test_isAtom_various():
    assert isAtom(Equals(x, y))
    assert isAtom(LT(a, Int(0)))
    assert not isAtom(Plus(x, y))
    assert not isAtom(And(Equals(x, y), LT(x, y)))
