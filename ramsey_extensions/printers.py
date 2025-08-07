from pysmt import formula
from pysmt.printers import HRPrinter, HRSerializer
from pysmt.exceptions import PysmtTypeError

from ramsey_extensions.operators import MOD_NODE_TYPE, RAMSEY_NODE_TYPE


class ExtendedPrinter(HRPrinter):
    """
    HRPrinter extension to serialize Ramsey quantifiers in S-expression style.
    """

    def __init__(self, stream, env=None):
        super().__init__(stream, env)
        self.functions[RAMSEY_NODE_TYPE] = self.walk_ramsey
        #self.functions[MOD_NODE_TYPE] = self.walk_mod

    def walk_ramsey(self, formula):
        """
        Print a Ramsey quantifier node:
            (ramsey (vars1) (vars2). body)
        """
        if formula.node_type() is not RAMSEY_NODE_TYPE:
            raise PysmtTypeError("Expected a RAMSEY node")

        var_groups = formula._content.payload
        if len(var_groups) != 2:
            raise PysmtTypeError(
                f"RAMSEY expects two variable groups, got {len(var_groups)}"
            )

        # Start quantifier
        self.write("(ramsey ")

        # Write each group: (v1, v2, ...)
        for gi, group in enumerate(var_groups):
            self.write("(")
            for vi, var in enumerate(group):
                yield var
                if vi < len(group) - 1:
                    self.write(", ")
            self.write(")")
            if gi < len(var_groups) - 1:
                self.write(" ")

        # Separator and body
        self.write(". ")
        yield formula.arg(0)
        self.write(")")

    def walk_mod(self, formula): return self.walk_nary(formula, " mod ")

    def walk_toint(self, formula):
        self.write("(to_int ")
        yield formula.arg(0)
        self.write(")")

class ExtendedSerializer(HRSerializer):
    """
    Serializer that uses ExtendedPrinter for Ramsey support.
    """
    PrinterClass = ExtendedPrinter
