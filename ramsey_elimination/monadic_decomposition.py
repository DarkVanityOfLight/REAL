from typing import List
from pysmt.shortcuts import And, Exists, FreshSymbol, Not, Or, is_sat
from pysmt.typing import INT, REAL
from ramsey_elimination.eliminate_ramsey import eliminate_ramsey
from ramsey_extensions.fnode import ExtendedFNode
from ramsey_extensions.shortcuts import Ramsey


def is_mondec(f: ExtendedFNode, is_mixed_separated=False):
    """
    Checks whether a formula 'f' is *monadically decomposable*.
    A formula is monadically decomposable if it can be expressed
    as a conjunction of formulas each depending on at most one variable.
    """
    free_vars: List[ExtendedFNode] = list(f.get_free_variables())

    # Trivial case: 0 or 1 variable → always decomposable
    if len(free_vars) < 2:
        return True

    # --- Duplicate variable sets ---
    # u and v represent two copies of the variable set
    u = [
        FreshSymbol(INT, f"u_{i}%s") if var.symbol_type() == INT else FreshSymbol(REAL, f"u_{i}%s")
        for i, var in enumerate(free_vars)
    ]
    v = [
        FreshSymbol(INT, f"v_{i}%s") if var.symbol_type() == INT else FreshSymbol(REAL, f"v_{i}%s")
        for i, var in enumerate(free_vars)
    ]

    # Substitute variables with u and v copies
    f_u = f.substitute({var: val for (var, val) in zip(free_vars, u)})
    f_v = f.substitute({var: val for (var, val) in zip(free_vars, v)})

    # --- Pairwise independence test ---
    # For each variable position i, check if its contribution can be separated
    for i in range(len(free_vars) - 1):
        w = FreshSymbol(free_vars[i].symbol_type(), "w_%s")  # fresh linking variable

        # Replace the i-th variable by w in both f_u and f_v
        f_u_w, f_v_w = f_u.substitute({u[i]: w}), f_v.substitute({v[i]: w})

        # Difference formula: detects mismatch when substituting w
        g = Or(And(f_u_w, Not(f_v_w)), And(Not(f_u_w), f_v_w))

        # Use Ramsey quantifier elimination to remove existential variable w
        elim = eliminate_ramsey(
            Ramsey(u[:i] + u[i+1:], v[:i] + v[i+1:], Exists([w], g)),
            is_mixed_separated
        )

        # If result is satisfiable -> f is not decomposable
        if is_sat(elim):
            return False

    # No witness of dependency found -> decomposable
    return True
