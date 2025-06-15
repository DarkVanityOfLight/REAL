

def free_variables_walk_ramsey(self, formula, args, **kwargs):
    vars = formula.quantifier_vars()
    vars = vars[0] + vars[1]
    return args[0].difference(formula.quantifier_vars())

def theory_walk_mod(self, formula, args, **kwargs):
    """Extends the Theory with Non-Linear, if needed."""
    assert len(args) == 2
    theory_out = args[0]
    for t in args[1:]:
        theory_out = theory_out.combine(t)

    # Check for non-linear
    _, right = formula.args()
    if len(right.get_free_variables()) != 0:
        theory_out.set_linear(False)

    theory_out = theory_out.set_difference_logic(False)
    return theory_out
