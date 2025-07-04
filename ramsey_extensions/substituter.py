from pysmt.substituter import MGSubstituter

class ExtendedMGSubstituter(MGSubstituter):

    def walk_mod(self, formula, args, **kwargs):
        substitutions = kwargs['substitutions']
        res = substitutions.get(formula, None)
        if res is None:
            res = self.mgr.Mod(args[0], args[1])
        return res

