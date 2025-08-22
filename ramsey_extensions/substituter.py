import pysmt.walkers
from pysmt.substituter import MGSubstituter

class ExtendedMGSubstituter(MGSubstituter):

    def walk_mod(self, formula, args, **kwargs):
        substitutions = kwargs['substitutions']
        res = substitutions.get(formula, None)
        if res is None:
            res = self.mgr.Mod(args[0], args[1])
        return res

    def walk_toint(self, formula, args, **kwargs):
        substitutions = kwargs['substitutions']
        res = substitutions.get(formula, None)
        if res is None:
            res = self.mgr.ToInt(args[0])
        return res

    def walk_ramsey(self, formula, args, **kwargs):
        substitutions = kwargs['substitutions']
        res = substitutions.get(formula, None)
        if res is None:
            qvars = ([pysmt.walkers.IdentityDagWalker.walk_symbol(self, v, args, **kwargs)
                for v in formula.quantifier_vars()[0]],
                     [pysmt.walkers.IdentityDagWalker.walk_symbol(self, v, args, **kwargs)
                for v in formula.quantifier_vars()[1]])

            res = self.mgr.Ramsey(*qvars, args[0])
        return res
