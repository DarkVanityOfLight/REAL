from pysmt.exceptions import PysmtTypeError
from pysmt.operators import INT_CONSTANT
from pysmt.typing import BOOL, INT, REAL
import pysmt.operators

from pysmt.type_checker import SimpleTypeChecker
from pysmt.walkers import handles

from ramsey_extensions.operators import MOD_NODE_TYPE, RAMSEY_NODE_TYPE


class ExtendedTypeChecker(SimpleTypeChecker):
    """
    Extend the PySMT type checker with the Ramsey quantifier.
    """

    def __init__(self, env=None):
        super().__init__(env)

    @handles(RAMSEY_NODE_TYPE)
    def walk_ramsey(self, formula, args, **kwargs):
        """
        Type check a given Ramsey quantifier.
        """
        # Expect exactly one Boolean body
        if len(args) != 1:
            raise PysmtTypeError(f"RAMSEY expects 1 Boolean body, got {len(args)} children")

        (body_type,) = args
        if body_type is not BOOL:
            raise PysmtTypeError(f"RAMSEY body must be Bool, got {body_type}")

        # Extract variable lists from payload
        var_lists = formula._content.payload
        if len(var_lists) != 2:
            raise PysmtTypeError(f"RAMSEY expects 2 var-lists, got {len(var_lists)}")

        # Ensure all vars share the same numeric type
        seen_type = None
        for i, var_list in enumerate(var_lists):
            for j, var in enumerate(var_list):
                t = self.get_type(var)
                if seen_type is None:
                    seen_type = t
                elif t is not seen_type:
                    raise PysmtTypeError(
                        f"RAMSEY var mismatch at var_lists[{i}][{j}]: got {t}, expected {seen_type}"
                    )

        # Numeric types must be Int or Real
        if seen_type not in (INT, REAL):
            raise PysmtTypeError(f"RAMSEY vars must be Int or Real, got {seen_type}")

        return BOOL


    @handles(MOD_NODE_TYPE)
    def walk_mod(self, formula, args, **kwargs):
        assert formula.arg(1).node_type() == INT_CONSTANT
        return self.walk_type_to_type(formula, args, INT, INT)
