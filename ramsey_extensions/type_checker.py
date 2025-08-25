from typing import Set
from pysmt.exceptions import PysmtTypeError
from pysmt.operators import INT_CONSTANT
from pysmt.typing import BOOL, INT, REAL, PySMTType
import pysmt.operators

from pysmt.type_checker import SimpleTypeChecker
from pysmt.walkers import handles

from ramsey_extensions.operators import MOD_NODE_TYPE, RAMSEY_NODE_TYPE, TOINT_NODE_TYPE


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

        left_vars, right_vars = var_lists
        if len(left_vars) != len(right_vars):
            raise PysmtTypeError(
                f"RAMSEY expects var-lists of equal length, got {len(left_vars)} and {len(right_vars)}"
            )

        # Ensure pairwise type matching and numeric type restriction
        for i, (lv, rv) in enumerate(zip(left_vars, right_vars)):
            lt, rt = lv.symbol_type(), rv.symbol_type()

            if lt != rt:
                raise PysmtTypeError(
                    f"RAMSEY var types must match pairwise: index {i} has {lt} vs {rt}"
                )
            if lt not in (INT, REAL):
                raise PysmtTypeError(
                    f"RAMSEY vars must be Int or Real, got {lt} at index {i}"
                )

        return BOOL


    @handles(MOD_NODE_TYPE)
    def walk_mod(self, formula, args, **kwargs):
        assert formula.arg(1).node_type() == INT_CONSTANT
        return self.walk_type_to_type(formula, args, INT, INT)

    @handles(TOINT_NODE_TYPE)
    def walk_real_to_int(self, formula, args, **kwargs):
        # pylint: disable=unused-argument
        return self.walk_type_to_type(formula, args, REAL, INT)
