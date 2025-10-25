from typing import Dict, List, Tuple, Union, cast
from pysmt.shortcuts import LT, And, Or, Plus, substitute
from pysmt import typing as typ

from ramsey_elimination.formula_utils import _fresh_vector
from ramsey_extensions.fnode import ExtendedFNode
from ramsey_extensions.shortcuts import Ramsey


def _create_quantifier_elimination_vars(
    ex_vars: Tuple[ExtendedFNode, ...],
    var_type: Union[typ._IntType, typ._RealType],
) -> Tuple[
    Dict[ExtendedFNode, ExtendedFNode],
    Tuple[ExtendedFNode, ...],
    Tuple[ExtendedFNode, ...],
    Tuple[ExtendedFNode, ...],
    Tuple[ExtendedFNode, ...],
]:
    """
    Create fresh vectors (v1, v2, w1, w2) and a substitution map
    for eliminating existential quantifiers under a Ramsey quantifier.

    Substitution rule: x_i |-> v1_i + w2_i
    """
    n = len(ex_vars)
    if n == 0:
        return {}, (), (), (), ()

    v1 = _fresh_vector("v1_%s", n, var_type)
    v2 = _fresh_vector("v2_%s", n, var_type)
    w1 = _fresh_vector("w1_%s", n, var_type)
    w2 = _fresh_vector("w2_%s", n, var_type)
    subs = {ex_vars[i]: Plus(v1[i], w2[i]) for i in range(n)}  # type: ignore

    return subs, tuple(v1), tuple(v2), tuple(w1), tuple(w2)


def eliminate_existential_quantifier(formula: ExtendedFNode) -> ExtendedFNode:
    """
    Unified elimination of existential quantifiers inside a Ramsey formula.

    Works for both uniform and mixed-typed cases:
      (ramsey (...) (...) (exists (...) phi))

    For each existential variable x_i, introduces fresh vectors v1,v2,w1,w2
    (per type) and substitutes x_i |-> v1_i + w2_i. Builds a new Ramsey formula
    with added pairwise distinctness constraints.
    """
    assert formula.is_ramsey()

    # If there's no existential quantifier, return unchanged
    if not formula.arg(0).is_exists():
        return formula

    ex_vars: List[ExtendedFNode] = list(formula.arg(0).quantifier_vars())
    subformula = formula.arg(0).arg(0)

    # Separate integer and real existential vars (for mixed cases)
    int_vars = tuple(v for v in ex_vars if v.symbol_type() == typ.INT)
    real_vars = tuple(v for v in ex_vars if v.symbol_type() == typ.REAL)

    # Generate substitutions for each type domain
    int_subs, int_v1, int_v2, int_w1, int_w2 = _create_quantifier_elimination_vars(int_vars, typ.INT)
    real_subs, real_v1, real_v2, real_w1, real_w2 = _create_quantifier_elimination_vars(real_vars, typ.REAL)

    # Merge substitution maps and apply to subformula
    substituted = substitute(subformula, {**int_subs, **real_subs})

    # Retrieve original Ramsey-bound variable tuples
    x_vars, y_vars = cast(Tuple[Tuple[ExtendedFNode, ...], Tuple[ExtendedFNode, ...]], formula.quantifier_vars())

    # Extend with all newly introduced variables
    new_x = real_v1 + real_v2 + int_v1 + int_v2 + x_vars
    new_y = real_w1 + real_w2 + int_w1 + int_w2 + y_vars

    # Enforce pairwise distinctness between corresponding x/y pairs
    distinct = Or([Or(LT(x, y), LT(y, x)) for x, y in zip(x_vars, y_vars)])

    return Ramsey(new_x, new_y, And(substituted, distinct))
