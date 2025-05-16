from pysmt.shortcuts import Int, Symbol, And, Equals, LT, Not, Plus, Times, Minus
from pysmt.typing import INT

# Import the functions under test
from RamseyQuantors.formula_utils import (
    isAtom,
    collect_atoms,
    collect_sum_terms,
    reconstruct_from_coeff_map,
    apply_to_atoms
)

# Create some sample symbols
x = Symbol('x', INT)
y = Symbol('y', INT)
a = Symbol('a', INT)


def test_isAtom_basic_relations():
    # Equality is an atom
    eq = Equals(x, y)
    assert isAtom(eq)
    # Less-than is an atom
    lt = LT(x, Int(5))
    assert isAtom(lt)
    # Negation of equality is NOT considered an atom by default
    neg_eq = Not(Equals(x, y))
    assert not isAtom(neg_eq)


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


def test_collect_sum_terms_simple():
    # 5*x - 3*a + 7
    term = Plus(Times(Int(5), x), Times(Int(-3), a), Int(7))
    coeffs, const = collect_sum_terms(term)
    assert coeffs[x] == 5
    assert coeffs[a] == -3
    assert const == 7


def test_collect_sum_terms_nested_minus():
    # x - (2*y - 4) => x - 2*y + 4
    inner = Minus(Times(Int(2), y), Int(4))
    term = Minus(x, inner)
    coeffs, const = collect_sum_terms(term)
    assert coeffs[x] == 1
    assert coeffs[y] == -2
    assert const == 4


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
