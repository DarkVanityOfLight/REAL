import functools
from pysmt.smtlib.parser import SmtLibParser

def open_(fname):
    """Transparently handle .bz2 files."""
    if fname.endswith(".bz2"):
        import bz2
        return bz2.open(fname, "rt")
    return open(fname)


def get_formula(script_stream, environment=None):
    """
    Returns the formula asserted at the end of the given script

    script_stream is a file descriptor.
    """
    mgr = None
    if environment is not None:
        mgr = environment.formula_manager

    parser = ExtendedSmtLibParser(environment)
    script = parser.get_script(script_stream)
    return script.get_last_formula(mgr)


def get_formula_strict(script_stream, environment=None):
    """Returns the formula defined in the SMTScript.

    This function assumes that only one formula is defined in the
    SMTScript. It will raise an exception if commands such as pop and
    push are present in the script, or if check-sat is called more
    than once.
    """
    mgr = None
    if environment is not None:
        mgr = environment.formula_manager

    parser = ExtendedSmtLibParser(environment)
    script = parser.get_script(script_stream)
    return script.get_strict_formula(mgr)


def get_formula_fname(script_fname, environment=None, strict=True):
    """Returns the formula asserted at the end of the given script."""
    with open_(script_fname) as script:
        if strict:
            return get_formula_strict(script, environment)
        else:
            return get_formula(script, environment)

class ExtendedSmtLibParser(SmtLibParser):
    def __init__(self, environment=None, interactive=False):
        super().__init__(environment, interactive)
        self.interpreted["ramsey"] = self._enter_ramsey
        self.interpreted["mod"] = self._operator_adapter(self._modulo)


    def _enter_ramsey(self, stack, tokens, key):
        # 1) Parse the sort (either T or (T))
        tok = tokens.consume()
        if tok == '(':
            ty = self.parse_type(tokens, "expression")
            self.consume_closing(tokens, "expression")
        else:
            tokens.add_extra_token(tok)
            ty = self.parse_type(tokens, "expression")

        # 2) First var-list: (x1 x2 …)
        self.consume_opening(tokens, "expression")
        vrs1 = []
        while True:
            name = tokens.consume()
            if name == ')':
                break
            var = self._get_quantified_var(name, ty)
            self.cache.bind(name, var)
            vrs1.append((name, var))

        # 3) Second var-list: (y1 y2 …)
        self.consume_opening(tokens, "expression")
        vrs2 = []
        while True:
            name = tokens.consume()
            if name == ')':
                break
            var = self._get_quantified_var(name, ty)
            self.cache.bind(name, var)
            vrs2.append((name, var))

        # 4) Parse the embedded formula under these bindings
        body = self.get_expression(tokens)

        # 6) Push exit-handler + its arguments
        stack[-1].append(self._exit_ramsey)
        stack[-1].append(vrs1)
        stack[-1].append(vrs2)
        stack[-1].append(body)

    def _exit_ramsey(self, vrs1, vrs2, body):
        # Unbind the names
        for name, _ in vrs1 + vrs2:
            self.cache.unbind(name)

        # Extract Symbol objects from the binding lists
        syms1 = [var for _, var in vrs1]
        syms2 = [var for _, var in vrs2]

        return self.env.formula_manager.Ramsey(syms1, syms2, body)

    def _modulo(self, left, right):
        return self.env.formula_manager.Mod(left, right)
