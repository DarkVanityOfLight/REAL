from typing import List
from pysmt.shortcuts import And, Exists, FreshSymbol, Not, Or, Solver, Symbol, is_sat, substitute
from pysmt.typing import INT, REAL
from ramsey_elimination.eliminate_ramsey import eliminate_ramsey
from ramsey_extensions.fnode import ExtendedFNode
from ramsey_extensions.shortcuts import Ramsey

def is_mondec(f: ExtendedFNode, is_mixed_separated=False):
    """
    Checks if the given formula 'f' is monadically decomposable.
    """
    free_vars: List[ExtendedFNode] = list(f.get_free_variables())

    if len(free_vars) < 2:
        return True # Formulas with 0 or 1 variables are trivially decomposable.


    u = [
        FreshSymbol(INT, f"u_{i}%s") if var.symbol_type() == INT else FreshSymbol(REAL, f"u_{i}%s")
        for i, var in enumerate(free_vars)
    ]
    v = [
        FreshSymbol(INT, f"v_{i}%s") if var.symbol_type() == INT else FreshSymbol(REAL, f"v_{i}%s")
        for i, var in enumerate(free_vars)
    ]

    f_u = f.substitute({var: u for (var, u)  in zip(free_vars, u)})
    f_v = f.substitute({var: v for (var, v)  in zip(free_vars, v)})

    for i in range(len(free_vars)-1):
        w = FreshSymbol(free_vars[i].symbol_type(), "w_%s")

        f_u_w, f_v_w = f_u.substitute({u[i]: w}), f_v.substitute({v[i]: w})
        g = Or(And(f_u_w, Not(f_v_w)), And(Not(f_u_w), f_v_w))

        elim = eliminate_ramsey(Ramsey(u[:i] + u[i+1:], v[:i] + v[i+1:], Exists([w], g)), is_mixed_separated)

        if is_sat(elim):
            return False

    return True




