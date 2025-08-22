from typing import Dict, List, Tuple, Union, cast

from pysmt.shortcuts import LT, And, Or, Plus, substitute
from pysmt import typing as typ

from ramsey_elimination.formula_utils import _fresh_vector
from ramsey_extensions.fnode import ExtendedFNode
from ramsey_extensions.shortcuts import Ramsey

def _create_quantifier_elimination_vars(existential_vars: Tuple[ExtendedFNode, ...], typ: Union[typ._IntType, typ._RealType]) -> Tuple[Dict[ExtendedFNode, ExtendedFNode], Tuple[ExtendedFNode, ...], Tuple[ExtendedFNode, ...], Tuple[ExtendedFNode, ...], Tuple[ExtendedFNode, ...]]:
    v1, v2, w1, w2 = [], [], [], []
    substitution_map = {}

    v1 = _fresh_vector("v1_%s", len(existential_vars), typ)
    v2 = _fresh_vector("v2_%s", len(existential_vars), typ)
    w1 = _fresh_vector("w1_%s", len(existential_vars), typ)
    w2 = _fresh_vector("w2_%s", len(existential_vars), typ)

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
    # Assume (ramsey (...) (...) (exists (...) phi)))
    assert formula.is_ramsey()

    if not formula.arg(0).is_exists():
        return formula

    ex_vars: List[ExtendedFNode] = formula.arg(0).quantifier_vars()
    int_vars = filter(lambda v: v.symbol_type() == typ.INT, ex_vars)
    real_vars = filter(lambda v: v.symbol_type() == typ.REAL, ex_vars)

    int_substitution_map, int_v1, int_v2, int_w1, int_w2 = _create_quantifier_elimination_vars(tuple(int_vars), typ.INT)
    real_substitution_map, real_v1, real_v2, real_w1, real_w2 = _create_quantifier_elimination_vars(tuple(real_vars), typ.REAL)

    subformula = formula.arg(0).arg(0)
    substituted_formula = substitute(subformula, int_substitution_map | real_substitution_map)

    new_x = real_v1 + real_v2 + int_v1 + int_v2 + formula.quantifier_vars()[0]
    new_y = real_w1 + real_w2 + int_w1 + int_w2 + formula.quantifier_vars()[1]

    #Ensure pairwise distinct subclique
    pairwise_distinct = Or([Or(LT(x, y), LT(y, x)) for x, y in zip(*formula.quantifier_vars())])
    return Ramsey(new_x , new_y, And(substituted_formula, pairwise_distinct))
