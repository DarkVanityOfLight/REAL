import enum
from pysmt.shortcuts import And, Exists, FreshSymbol, Not, Or, Solver, Symbol, is_sat
from pysmt.typing import INT, REAL
from ramsey_elimination.eliminate_ramsey import eliminate_ramsey
from ramsey_extensions.fnode import ExtendedFNode
from ramsey_extensions.shortcuts import Ramsey

def is_mondec(f: ExtendedFNode):
    """
    Checks if the given formula 'f' is monadically decomposable.

    The formula 'f' is monadically decomposable if and only if for every free
    variable 'x_i' in 'f', the number of its equivalence classes is finite.

    This is checked by verifying that for each 'x_i', the formula expressing
    "there exists an infinite sequence of distinguishable values for x_i"
    is UNSATISFIABLE.
    """
    free_vars = f.get_free_variables()

    if len(free_vars) < 2:
        return True # Formulas with 0 or 1 variables are trivially decomposable.

    # Iterate through each free variable to test it.
    for i, var_to_test in enumerate(free_vars):
        # --- Step 1: Construct the "Distinguishability" Formula delta(x', x'') --- 

        # Create two fresh symbols (x', x'') to represent two different values for the variable we are testing.
        x_prime = FreshSymbol(var_to_test.symbol_type(), f"x_prime_{i}_%s")
        x_double_prime = FreshSymbol(var_to_test.symbol_type(), f"x_double_prime_{i}_%s")

        # Gather all OTHER variables. These will be existentially quantified.
        other_vars = free_vars[:i] + free_vars[i+1:]
        y_vars = [FreshSymbol(v.symbol_type(), f"y_{j}_%s") for j, v in enumerate(other_vars)]

        # Create two versions of the original formula 'f':
        # 1. Where var_to_test = x' and other_vars = y_vars
        substitutions1 = {var_to_test: x_prime}
        substitutions1.update({ov: yv for ov, yv in zip(other_vars, y_vars)})
        phi_at_x_prime = f.substitute(substitutions1)

        # 2. Where var_to_test = x'' and other_vars = y_vars
        substitutions2 = {var_to_test: x_double_prime}
        substitutions2.update({ov: yv for ov, yv in zip(other_vars, y_vars)})
        phi_at_x_double_prime = f.substitute(substitutions2)

        # The core of delta: are x' and x'' distinguishable?
        # This is not(phi(x', y) <-> phi(x'', y))
        distinguishability = Or(
            And(phi_at_x_prime, Not(phi_at_x_double_prime)),
            And(Not(phi_at_x_prime), phi_at_x_double_prime)
        )

        # Existentially quantify over the 'other' variables to create the final δ formula.
        # delta(x', x'') := exists y: not(phi(x', y) <-> phi(x'', y))
        delta_formula = Exists(y_vars, distinguishability)

        # --- Step 2: Formulate the "Infinite-Classes" Condition using a Ramsey Quantifier ---
        # mu := ramsey (x', x''): delta(x', x'')
        mu_formula = Ramsey([x_prime], [x_double_prime], delta_formula)

        # --- Step 3 & 4: Eliminate the Quantifier and Check Satisfiability ---
        # This step assumes you have an `eliminate_ramsey` function.
        mu_eliminated = eliminate_ramsey(mu_formula)

        if is_sat(mu_eliminated):
            # If the formula is SATISFIABLE, it means there IS an infinite
            # number of distinguishable values for 'var_to_test'.
            # Therefore, 'f' is NOT monadically decomposable. We can stop early.
            return False

    # If the loop completes without finding any variable with infinite classes,
    # then the formula IS monadically decomposable.
    return True
