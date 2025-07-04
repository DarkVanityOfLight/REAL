import pytest

from pysmt.shortcuts import Equals, Int, Symbol, And, Or, ForAll, Exists, LT, LE, GT, Implies, Iff, Not, Times, Plus, get_env
from pysmt.typing import BOOL, INT
import pysmt.operators as operators

from ramsey_extensions.shortcuts import Mod

from ramsey_elimination.formula_utils import is_atom, apply_to_atoms
from ramsey_elimination.simplifications import (
    arithmetic_solver,
    make_int_input_format,
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

# --- Tests for is_atom and apply_to_atoms on mixed formulas ---

def test_apply_to_atoms_ignores_non_atoms():
    # Arithmetic term is not treated as atom
    term = Plus(x, y)
    out = apply_to_atoms(term, lambda atm: Int(99))
    # Plus stays unchanged
    assert out.node_type() == operators.PLUS and set(out.args()) == {x, y}


def test_is_atom_various():
    assert is_atom(Equals(x, y))
    assert is_atom(LT(a, Int(0)))
    assert not is_atom(Plus(x, y))
    assert not is_atom(And(Equals(x, y), LT(x, y)))



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
