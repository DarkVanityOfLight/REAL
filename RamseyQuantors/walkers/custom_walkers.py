

def free_variables_walk_ramsey(self, formula, args, **kwargs):
    vars = formula.quantifier_vars()
    vars = vars[0] + vars[1]
    return args[0].difference(formula.quantifier_vars())


