from typing import Dict, List, Tuple, Union, cast

from pysmt.shortcuts import LT, And, Or, Plus, substitute
from pysmt import typing as typ

from ramsey_elimination.formula_utils import _vector
from ramsey_extensions.fnode import ExtendedFNode
from ramsey_extensions.shortcuts import Ramsey

def _create_quantifier_elimination_vars(existential_vars: Tuple[ExtendedFNode, ...], typ: Union[typ._IntType, typ._RealType]) -> Tuple[Dict[ExtendedFNode, ExtendedFNode], Tuple[ExtendedFNode, ...], Tuple[ExtendedFNode, ...], Tuple[ExtendedFNode, ...], Tuple[ExtendedFNode, ...]]:
    v1, v2, w1, w2 = [], [], [], []
    substitution_map = {}

    v1 = _vector("v1", len(existential_vars), typ)
    v2 = _vector("v2", len(existential_vars), typ)
    w1 = _vector("w1", len(existential_vars), typ)
    w2 = _vector("w2", len(existential_vars), typ)

    substitution_map : dict[ExtendedFNode, ExtendedFNode] = {existential_vars[i]: Plus(v1[i], w2[i]) for i in range(len(existential_vars))} #type: ignore
    return (substitution_map, tuple(v1), tuple(v2), tuple(w1), tuple(w2))

def eliminate_existential_quantifier(formula: ExtendedFNode):
    assert formula.is_ramsey()
    assert formula.arg(0).is_exists()

    T = formula.arg(0).quantifier_vars()[0].get_type()

    exvars = formula.arg(0).quantifier_vars()
    substitution_map, v1, v2, w1, w2 = _create_quantifier_elimination_vars(exvars, T)

    # Assume (ramsey (...) (...)  (exists (...) phi))
    # We extract phi
    subformula = formula.arg(0).arg(0)

    # Substitute each variable x_i bound by the existential quantifier with v1_i + w2_i
    substituted_formula = subformula.substitute(substitution_map)
    
    # Get the current variables bound originally by the ramsey quantifier
    x, y = cast(Tuple[Tuple[ExtendedFNode], Tuple[ExtendedFNode]], formula.quantifier_vars())

    # Add the newly introduced variables
    new_x =  x + v1 + v2
    new_y = y + w1 + w2

    #Ensure pairwise distinct subclique
    pairwise_distinct = Or([Or(LT(x[i], y[i]), LT(y[i], x[i])) for i in range(len(x))])

    # Create a new Ramsey quantifier now with the substituted formula, the pairwise distinctnes and the two new vectors of bound variables
    return Ramsey(new_x, new_y, And(substituted_formula, pairwise_distinct))

def eliminate_mixed_existential_quantifier(formula: ExtendedFNode):
    # Assume (ramsey (...) (...)  (ramsey (...) (...) (exists (...) phi)))
    assert formula.is_ramsey()
    assert formula.arg(0).is_ramsey()
    assert formula.arg(0).arg(0).is_exists()

    real_ram, int_ram = (formula, formula.arg(0)) if formula.quantifier_vars()[0][0].get_type() == typ.REAL else (formula.arg(0), formula)

    int_vars: List[ExtendedFNode]
    real_vars: List[ExtendedFNode]
    int_vars, real_vars = [], []
    for var in formula.arg(0).arg(0).quantifier_vars():
        T = var.get_type()
        if T == typ.REAL:
            real_vars.append(var)
        elif T == typ.INT:
            int_vars.append(var)

    int_substitution_map, int_v1, int_v2, int_w1, int_w2 = _create_quantifier_elimination_vars(tuple(int_vars), typ.INT)
    real_substitution_map, real_v1, real_v2, real_w1, real_w2 = _create_quantifier_elimination_vars(tuple(real_vars), typ.REAL)

    subformula = formula.arg(0).arg(0).arg(0)
    substituted_formula = substitute(subformula, int_substitution_map | real_substitution_map)

    x_real, y_real = cast(Tuple[Tuple[ExtendedFNode], Tuple[ExtendedFNode]], real_ram.quantifier_vars())
    x_int, y_int = cast(Tuple[Tuple[ExtendedFNode], Tuple[ExtendedFNode]], int_ram.quantifier_vars())

    x_new_real = x_real + real_v1 + real_v2
    y_new_real = y_real + real_w1 + real_w2

    x_new_int = x_int + int_v1 + int_v2
    y_new_int = y_int + int_w1 + int_w2

    #Ensure pairwise distinct subclique
    pairwise_distinct_real = Or([Or(LT(x_real[i], y_real[i]), LT(y_real[i], x_real[i])) for i in range(len(x_real))])
    pairwise_distinct_int = Or([Or(LT(x_int[i], y_int[i]), LT(y_int[i], x_int[i])) for i in range(len(x_int))])

    return Ramsey(x_new_real, y_new_real, Ramsey(x_new_int, y_new_int, And(substituted_formula, pairwise_distinct_int, pairwise_distinct_real)))
