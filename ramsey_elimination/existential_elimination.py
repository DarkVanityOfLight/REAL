from typing import Dict, Tuple, Union, cast

from pysmt.shortcuts import LT, And, Or, Plus
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

    substitution_map = {existential_vars[i]: Plus(v1[i], w2[i]) for i in range(len(existential_vars))}
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
