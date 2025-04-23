from pysmt.shortcuts import *

def Ramsey(vv1, vv2, formula):
    """
    Shorthand for creating a Ramsey quantifier node:
        Ramsey(vv1, vv2). formula

    Args:
        vv1 (Sequence[FNode]): First group of bound variables.
        vv2 (Sequence[FNode]): Second group of bound variables.
        formula (FNode): Boolean formula over bound variables.

    Returns:
        FNode: A RAMSEY quantifier node, as produced by the environment's FormulaManager.
    """
    fm = get_env().formula_manager
    return fm.Ramsey(vv1, vv2, formula)
