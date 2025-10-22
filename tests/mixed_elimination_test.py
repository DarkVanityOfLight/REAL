
from ramsey_elimination.formula_utils import map_atoms
from ramsey_elimination.mixed_elimination import compute_seperation

from ramsey_extensions.shortcuts import *

def _validate_separation(f):
    def validate_atom(atom):
        assert len({v.get_type() for v in atom.get_free_variables()}) <= 1
        return atom

    map_atoms(f, validate_atom)
    return True

def _general_seperation(f):
    _validate_separation(compute_seperation(f))

def test_simple_lt():
    x = Symbol("x", REAL)
    y = Symbol("y", REAL)

    # 2. Define the input formula
    # f = 2*x + (-0.5)*y <= 3
    two_x = Times(Real(2), x)
    half_y = Times(Real(-0.5), y)
    lhs = Plus(two_x, half_y)
    rhs = Real(3)
    
    original_formula = LT(lhs, rhs)
    _general_seperation(original_formula)

def test_x_eq_5():
    x_eq_5 = Equals(Symbol("x", REAL), Real(5))
    _general_seperation(x_eq_5)

def test_complex():
    x, y, z = Symbol("x", REAL), Symbol("y", REAL), Symbol("z", REAL)
    f_complex_ineq = LT(Plus(Times(Real(3), x), Times(Real(-2), y), z), Real(10))
    _general_seperation(f_complex_ineq)

def test_floor():
    x, y = Symbol("x", REAL), Symbol("y", INT)
    f_floor = Equals(ToInt(Plus(x, Real(0.5))), y)
    _general_seperation(f_floor)

def test_mixed():
    x_int = Symbol("x_int", INT)
    y_real = Symbol("y_real", REAL)
    f_mixed = LT(Plus(ToReal(x_int), y_real), Real(5.5))
    _general_seperation(f_mixed)

def test_conjunct():
    x, y, z = Symbol("x", REAL), Symbol("y", REAL), Symbol("z", REAL)
    f_conj = And(LT(Times(Real(2), x), y), LT(y, Times(Real(3), z)))
    _general_seperation(f_conj)





    
