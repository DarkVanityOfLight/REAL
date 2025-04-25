import functools
from pysmt.smtlib.parser import SmtLibParser
from RamseyQuantors.operators import MOD_NODE_TYPE, RAMSEY_QUANTIFIER_NAME

class ExtendedSmtLibParser(SmtLibParser):
    def __init__(self, environment=None, interactive=False):
        super().__init__(environment, interactive)
        # Register the custom "ramsey" operator
        self.interpreted[RAMSEY_QUANTIFIER_NAME] = self._enter_ramsey
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
