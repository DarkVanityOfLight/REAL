from pysmt.shortcuts import Int, Symbol, And, Equals, LT, Not, Plus, Times, Minus
from pysmt.typing import INT
import pytest

# Import the functions under test
from ramsey_elimination.formula_utils import (
    is_atom,
    collect_atoms,
    reconstruct_from_coeff_map,
    apply_to_atoms,
    ast_to_terms
)

# Create some sample symbols
x = Symbol('x', INT)
y = Symbol('y', INT)
a = Symbol('a', INT)


def test_is_atom_basic_relations():
    # Equality is an atom
    eq = Equals(x, y)
    assert is_atom(eq)
    # Less-than is an atom
    lt = LT(x, Int(5))
    assert is_atom(lt)
    # Negation of equality is NOT considered an atom by default
    neg_eq = Not(Equals(x, y))
    assert not is_atom(neg_eq)


def test_collect_atoms_partitioning():
    # Build a formula with an equality, a negated eq, and an inequality
    mod_eq = Equals(x, y)  # assume no MOD_NODE_TYPE in tests
    neg_mod = Not(Equals(a, Int(3)))
    ineq = LT(a, Int(10))
    formula = And(mod_eq, neg_mod, ineq)

    eqs, modeqs, ineqs = collect_atoms(formula)
    # We expect one pure equality, one "mod" equality (negated), and one inequality
    assert eqs == (mod_eq,)
    assert neg_mod in modeqs
    assert ineqs == (ineq,)

def test_reconstruct_from_coeff_map_zero():
    # All zero coefficients and zero constant
    empty = reconstruct_from_coeff_map({}, 0)
    assert empty.is_int_constant() and empty.constant_value() == 0


def test_reconstruct_from_coeff_map_mixed():
    m = {x: 1, y: 2}
    node = reconstruct_from_coeff_map(m, 3)
    # Should equal Plus(x, Times(2, y), 3)
    # Check structure
    assert node.is_plus()
    args = set(node.args())
    assert x in args
    assert Times(Int(2), y) in args
    assert Int(3) in args


def test_apply_to_atoms_replaces_atoms():
    # And(x < 5, Equals(y, 1), Plus(x,y) > Int(0))
    f = And(LT(x, Int(5)), Equals(y, Int(1)), LT(Plus(x, y), Int(0)))
    transformed = apply_to_atoms(f, lambda atm: Equals(Int(42), Int(42)))
    # All atoms replaced by Int(42) == Int(42)
    # The resulting tree is a conjunction of three Int(42) == Int(42)
    assert transformed.is_and()
    for arg in transformed.args():
        assert arg == Equals(Int(42), Int(42))


@ pytest.mark.parametrize("value", [0, 1, -5, 42])
def test_int_constant(value):
    node = Int(value)
    terms, const = ast_to_terms(node)
    assert terms == {}
    assert const == value

@ pytest.mark.parametrize("name", ["x", "y", "z"])
def test_symbol(name):
    sym = Symbol(name, INT)
    terms, const = ast_to_terms(sym)
    assert const == 0
    assert terms == {sym: 1}

@ pytest.mark.parametrize("args, expected_terms, expected_const", [
    ([Int(1), Int(2), Int(3)], {}, 6),
    ([Symbol('x', INT), Int(3)], {Symbol('x', INT): 1}, 3),
    ([Symbol('x', INT), Symbol('x', INT)], {Symbol('x', INT): 2}, 0),
])
def test_plus(args, expected_terms, expected_const):
    node = Plus(args)
    terms, const = ast_to_terms(node)
    assert const == expected_const
    assert terms == expected_terms

@ pytest.mark.parametrize("expr, expected_terms, expected_const", [
    (Minus(Int(5), Int(2)), {}, 3),
    (Minus(Symbol('x', INT), Int(2)), {Symbol('x', INT): 1}, -2),
    (Minus(Symbol('x', INT), Symbol('x', INT)), {Symbol('x', INT): 0}, 0),
])
def test_minus(expr, expected_terms, expected_const):
    terms, const = ast_to_terms(expr)
    assert const == expected_const
    assert terms == {s: c for s, c in expected_terms.items() if c != 0}

@ pytest.mark.parametrize("expr, expected_terms, expected_const", [
    (Times([Int(3), Int(4)]), {}, 12),
    (Times([Int(3), Symbol('x', INT)]), {Symbol('x', INT): 3}, 0),
    (Times([Symbol('x', INT), Int(5)]), {Symbol('x', INT): 5}, 0),
])
def test_times(expr, expected_terms, expected_const):
    terms, const = ast_to_terms(expr)
    print(terms, const)
    assert const == expected_const
    assert terms == expected_terms


def test_times_invalid():
    # x * y should raise ValueError
    expr = Times([Symbol('x', INT), Symbol('y', INT)])
    with pytest.raises(ValueError):
        ast_to_terms(expr)
