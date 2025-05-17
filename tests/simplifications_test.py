
import pytest
from pysmt.shortcuts import Equals, Int, Symbol, And, Or, ForAll, Exists, LT, LE, GT, Implies, Iff, Not, Times, Plus, get_env
from pysmt.typing import BOOL, INT
import pysmt.operators as operators
from RamseyQuantors.formula_utils import isAtom, apply_to_atoms
from RamseyQuantors.shortcuts import Mod
from RamseyQuantors.simplifications import (
    arithmetic_solver,
    int_inequality_rewriter,
    make_int_input_format,
    push_negations_inside
)

get_env().enable_infix_notation = True
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



def test_le_rewrite():
    x, y = Symbol("x", INT), Symbol("y", INT)
    input_formula = LE(x, y)
    expected = LT(x, Plus(y, Int(1)))
    assert make_int_input_format(input_formula) == expected

def test_negated_le():
    x, y = Symbol("x", INT), Symbol("y", INT)
    input_formula = Not(LE(x, y))
    expected = LT(y, x)
    assert make_int_input_format(input_formula) == expected

def test_negated_lt():
    x, y = Symbol("x", INT), Symbol("y", INT)
    input_formula = Not(LT(x, y))
    expected = LT(y, Plus(x, Int(1)))
    assert make_int_input_format(input_formula) == expected

def test_negated_equals_no_mod():
    a, b = Symbol("a", INT), Symbol("b", INT)
    input_formula = Not(Equals(a, b))
    expected = Or(LT(a, b), LT(b, a))
    assert make_int_input_format(input_formula) == expected

def test_negated_equals_with_mod():
    c, m, b = Symbol("c", INT), Int(2), Symbol("b", INT)
    mod = Mod(c, m)
    input_formula = Not(Equals(mod, b))
    # Should remain ¬(c mod 2 = b)
    print(make_int_input_format(input_formula))
    assert make_int_input_format(input_formula) == Not(Equals(mod, b))

def test_negated_and():
    A, B = Symbol("A", BOOL), Symbol("B", BOOL)
    input_formula = Not(And(A, B))
    expected = Or(Not(A), Not(B))
    res = make_int_input_format(input_formula)
    assert res == expected

def test_negated_or():
    A, B = Symbol("A", BOOL), Symbol("B", BOOL)
    input_formula = Not(Or(A, B))
    expected = And(Not(A), Not(B))
    res = make_int_input_format(input_formula)
    assert res == expected

def test_negated_forall():
    x = Symbol("X", BOOL)
    body = x
    input_formula = Not(ForAll([x], body))
    expected = Exists([x], Not(body))
    assert make_int_input_format(input_formula) == expected

def test_negated_exists():
    x = Symbol("X", BOOL)
    body = x
    input_formula = Not(Exists([x], body))
    expected = ForAll([x], Not(body))
    assert make_int_input_format(input_formula) == expected

def test_negated_implies():
    A, B = Symbol("A", BOOL), Symbol("B", BOOL)
    input_formula = Not(Implies(A, B))
    expected = And(A, Not(B))
    assert make_int_input_format(input_formula) == expected

def test_negated_iff():
    A, B = Symbol("A", BOOL), Symbol("B", BOOL)
    input_formula = Not(Iff(A, B))
    expected = And(Or(Not(A), Not(B)), Or(A, B))
    assert make_int_input_format(input_formula) == expected

def test_double_negation():
    A, B = Symbol("A", BOOL), Symbol("B", BOOL)
    input_formula = Not(Not(A))
    assert make_int_input_format(input_formula) == A

def test_mod_in_both_sides():
    x, y = Symbol("x", INT), Symbol("y", INT)
    mod_x = Mod(x, Int(2))
    mod_y = Mod(y, Int(3))
    input_formula = Not(Equals(mod_x, mod_y))
    # Should remain ¬(x mod 2 = y mod 3)
    assert make_int_input_format(input_formula) == Not(Equals(mod_x, mod_y))

def test_nested_operations():
    x, y, a, b = Symbol("x", INT), Symbol("y", INT), Symbol("a", INT), Symbol("b", INT)
    mod = Mod(b, Int(5))
    inner_and = And(LE(x, y), Equals(a, mod))
    input_formula = Not(inner_and)
    expected = Or(LT(y, x), Not(Equals(a, mod)))
    assert make_int_input_format(input_formula) == expected


test_negated_and()
print("Done")
