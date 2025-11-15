import pytest

from pysmt.shortcuts import Equals, Int, Symbol, And, Or, ForAll, Exists, LT, LE, GT, Implies, Iff, Not, Times, Plus, get_env
from pysmt.typing import BOOL, INT
import pysmt.operators as operators

from ramsey_extensions.shortcuts import Mod

from ramsey_elimination.formula_utils import is_atom, map_atoms
from ramsey_elimination.simplifications import (
    arithmetic_solver,
    make_int_input_format,
)


class TestArithmeticSolver:
    """Test class for arithmetic_solver function"""
    
    def test_arithmetic_solver_simple(self, int_symbols):
        """Test basic arithmetic solver functionality"""
        x = int_symbols['x']
        a = int_symbols['a']
        b = int_symbols['b']
        
        # left: 5*x + 2*a , right: 3*x + 7*b , vars = {x}
        left = {x: 5, a: 2}
        right = {x: 3, b: 7}
        left_const = 4
        right_const = 10
        new_left, new_right, const = arithmetic_solver(left, left_const, right, right_const, {x})
        
        # x-coefficient: 5 - 3 = 2
        assert new_left == {x: 2}
        # non-vars: a and b on right: b:7, a:-2
        assert self._map_eq(new_right, {a: -2, b: 7})
        # constant part: right_const - left_const
        assert const == 6

    def _map_eq(self, m1, m2):
        """Helper function for comparing coefficient maps"""
        return all(m1.get(k, 0) == v for k, v in m2.items()) and all(m2.get(k, 0) == v for k, v in m1.items())


class TestFormulaUtils:
    """Test class for formula utility functions"""
    
    def test_apply_to_atoms_ignores_non_atoms(self, int_symbols):
        """Test that apply_to_atoms ignores non-atomic terms"""
        x = int_symbols['x']
        y = int_symbols['y']
        
        # Arithmetic term is not treated as atom
        term = Plus(x, y)
        out = map_atoms(term, lambda atm: Int(99))
        # Plus stays unchanged
        assert out.node_type() == operators.PLUS and set(out.args()) == {x, y}

    def test_is_atom_various(self, int_symbols):
        """Test is_atom function with various formula types"""
        x = int_symbols['x']
        y = int_symbols['y']
        a = int_symbols['a']
        
        assert is_atom(Equals(x, y))
        assert is_atom(LT(a, Int(0)))
        assert not is_atom(Plus(x, y))
        assert not is_atom(And(Equals(x, y), LT(x, y)))


class TestIntInputFormat:
    """Test class for make_int_input_format function"""
    
    def test_le_rewrite(self, int_symbols):
        """Test LE rewriting to LT"""
        x, y = int_symbols['x'], int_symbols['y']
        input_formula = LE(x, y)
        expected = LT(x, Plus(y, Int(1)))
        assert make_int_input_format(input_formula) == expected

    def test_negated_le(self, int_symbols):
        """Test negated LE rewriting"""
        x, y = int_symbols['x'], int_symbols['y']
        input_formula = Not(LE(x, y))
        expected = LT(y, x)
        assert make_int_input_format(input_formula) == expected

    def test_negated_lt(self, int_symbols):
        """Test negated LT rewriting"""
        x, y = int_symbols['x'], int_symbols['y']
        input_formula = Not(LT(x, y))
        expected = LT(y, Plus(x, Int(1)))
        assert make_int_input_format(input_formula) == expected

    def test_negated_equals_no_mod(self, int_symbols):
        """Test negated equality without modulo"""
        a, b = int_symbols['a'], int_symbols['b']
        input_formula = Not(Equals(a, b))
        expected = Or(LT(a, b), LT(b, a))
        assert make_int_input_format(input_formula) == expected

    def test_negated_equals_with_mod(self, int_symbols):
        """Test negated equality with modulo (should remain unchanged)"""
        c, b = int_symbols['a'], int_symbols['b']  # reusing a as c
        m = Int(2)
        mod = Mod(c, m)
        input_formula = Not(Equals(mod, b))
        assert make_int_input_format(input_formula) == Not(Equals(mod, b))

    def test_negated_and(self, bool_symbols):
        """Test negated AND using De Morgan's law"""
        A, B = bool_symbols['A'], bool_symbols['B']
        input_formula = Not(And(A, B))
        expected = Or(Not(A), Not(B))
        res = make_int_input_format(input_formula)
        assert res == expected

    def test_negated_or(self, bool_symbols):
        """Test negated OR using De Morgan's law"""
        A, B = bool_symbols['A'], bool_symbols['B']
        input_formula = Not(Or(A, B))
        expected = And(Not(A), Not(B))
        res = make_int_input_format(input_formula)
        assert res == expected

    def test_negated_forall(self):
        """Test negated ForAll becomes Exists"""
        x = Symbol("X", BOOL)  # Local symbol with different name to avoid conflicts
        body = x
        input_formula = Not(ForAll([x], body))
        expected = Exists([x], Not(body))
        assert make_int_input_format(input_formula) == expected

    def test_negated_exists(self):
        """Test negated Exists becomes ForAll"""
        x = Symbol("X", BOOL)  # Local symbol with different name to avoid conflicts
        body = x
        input_formula = Not(Exists([x], body))
        expected = ForAll([x], Not(body))
        assert make_int_input_format(input_formula) == expected

    def test_negated_implies(self, bool_symbols):
        """Test negated implication"""
        A, B = bool_symbols['A'], bool_symbols['B']
        input_formula = Not(Implies(A, B))
        expected = And(A, Not(B))
        assert make_int_input_format(input_formula) == expected

    def test_negated_iff(self, bool_symbols):
        """Test negated biconditional"""
        A, B = bool_symbols['A'], bool_symbols['B']
        input_formula = Not(Iff(A, B))
        expected = Or(And(A, Not(B)), And(B, Not(A)))
        assert make_int_input_format(input_formula) == expected

    def test_double_negation(self, bool_symbols):
        """Test double negation elimination"""
        A = bool_symbols['A']
        input_formula = Not(Not(A))
        assert make_int_input_format(input_formula) == A

    def test_mod_in_both_sides(self, int_symbols):
        """Test modulo operations on both sides (should remain unchanged)"""
        x, y = int_symbols['x'], int_symbols['y']
        mod_x = Mod(x, Int(2))
        mod_y = Mod(y, Int(3))
        input_formula = Not(Equals(mod_x, mod_y))
        # Should remain ¬(x mod 2 = y mod 3)
        assert make_int_input_format(input_formula) == Not(Equals(mod_x, mod_y))

    def test_nested_operations(self, int_symbols):
        """Test nested logical operations"""
        x, y, a, b = int_symbols['x'], int_symbols['y'], int_symbols['a'], int_symbols['b']
        mod = Mod(b, Int(5))
        inner_and = And(LE(x, y), Equals(a, mod))
        input_formula = Not(inner_and)
        expected = Or(LT(y, x), Not(Equals(a, mod)))
        assert make_int_input_format(input_formula) == expected


@pytest.fixture
def int_symbols():
    """Fixture providing fresh integer symbols for tests that need them"""
    return {
        'x': Symbol('x', INT),
        'y': Symbol('y', INT),
        'z': Symbol('z', INT),
        'a': Symbol('a', INT),
        'b': Symbol('b', INT),
    }


@pytest.fixture
def bool_symbols():
    """Fixture providing fresh boolean symbols for tests that need them"""
    return {
        'A': Symbol('A', BOOL),
        'B': Symbol('B', BOOL),
        'C': Symbol('C', BOOL),
    }


# Example of using fixtures (if needed for more complex tests)
def test_with_fixture_example(int_symbols):
    """Example test showing how to use symbol fixtures"""
    x, y = int_symbols['x'], int_symbols['y']
    formula = Equals(x, y)
    assert is_atom(formula)
