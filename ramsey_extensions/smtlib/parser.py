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

        # Register new parsers
        self.interpreted["ramsey"] = self._enter_ramsey
        self.interpreted["mod"] = self._operator_adapter(self._modulo)
        self.interpreted["to_int"] = self._operator_adapter(self._to_int)


    def _enter_ramsey(self, stack, tokens, key):
        """
        Parse a (ramsey ...) construct.

        Supported syntaxes:
        1. Uniformly typed:
            (ramsey Int (x y) (a b) phi)
            -> all quantified variables share type Int

        2. Mixed (per-variable types, no explicit 'mixed' keyword):
            (ramsey ((x Int) (a Real)) ((y Int) (b Real)) phi)

        Parsing stages:
        1. Detect whether the first token after 'ramsey' is a type or a var-list.
            - If it's a bare type (e.g., Int), parse as uniform.
            - If it's a list of typed pairs ((x Int) ...), parse as mixed.
        2. Parse both variable lists, binding variables in cache.
        3. Parse the body expression.
        4. Push a deferred exit-handler (_exit_ramsey) that unbinds and constructs
            the Ramsey node at the end.
        """

        is_mixed = False
        ty = None

        # --- Step 1: detect typing mode ---
        tok = tokens.consume()
        if tok == '(':
            next_tok = tokens.peek()
            if next_tok == '(':
                # Starts with ((x Int) ...) → mixed mode
                is_mixed = True
                tokens.add_extra_token('(')  # put back for var-list parsing
            else:
                # Starts with (Int) → uniform mode
                ty = self.parse_type(tokens, "expression")
                self.consume_closing(tokens, "expression")
        else:
            # No parentheses → simple type like "Int"
            tokens.add_extra_token(tok)
            ty = self.parse_type(tokens, "expression")

        # --- Step 2: first var-list ---
        self.consume_opening(tokens, "expression")
        vrs1 = []
        while True:
            name = tokens.consume()
            if name == ')':
                break

            if is_mixed:
                # Expect tuples like (x Int)
                tokens.add_extra_token(name)
                self.consume_opening(tokens, "expression")
                vname = self.parse_atom(tokens, "expression")
                typename = self.parse_type(tokens, "expression")
                self.consume_closing(tokens, "expression")
                var = self._get_quantified_var(vname, typename)
            else:
                var = self._get_quantified_var(name, ty)
                vname = name

            self.cache.bind(vname, var)
            vrs1.append((vname, var))

        # --- Step 3: second var-list ---
        self.consume_opening(tokens, "expression")
        vrs2 = []
        while True:
            name = tokens.consume()
            if name == ')':
                break

            if is_mixed:
                tokens.add_extra_token(name)
                self.consume_opening(tokens, "expression")
                vname = self.parse_atom(tokens, "expression")
                typename = self.parse_type(tokens, "expression")
                self.consume_closing(tokens, "expression")
                var = self._get_quantified_var(vname, typename)
            else:
                var = self._get_quantified_var(name, ty)
                vname = name

            self.cache.bind(vname, var)
            vrs2.append((vname, var))

        # --- Step 4: parse body formula ---
        body = self.get_expression(tokens)

        # --- Step 5: push exit-handler ---
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

    def _to_int(self, arg):
        return self.env.formula_manager.ToInt(arg)
