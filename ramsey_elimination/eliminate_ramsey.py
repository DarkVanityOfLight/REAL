from enum import Enum, auto
from ramsey_elimination.integer_elimination import full_ramsey_elimination_int
from ramsey_elimination.mixed_elimination import (
    eliminate_mixed_ramsey_from_separated,
    full_mixed_ramsey_elimination,
)
from ramsey_elimination.real_elimination import full_ramsey_elimination_real
from ramsey_extensions.fnode import ExtendedFNode


class _RamseyTypes(Enum):
    """Internal enum distinguishing Ramsey quantifier domains."""
    INT = auto()
    REAL = auto()
    MIXED = auto()


def eliminate_ramsey(f: ExtendedFNode, is_mixed_separated=False) -> ExtendedFNode:
    """
    Perform quantifier elimination on a Ramsey formula node.

    Depending on the variable types of the first quantified set, this function
    delegates to the appropriate elimination routine for integers, reals, or
    mixed domains.

    Args:
        f: The Ramsey formula (ExtendedFNode) to eliminate. Must satisfy f.is_ramsey().
        is_mixed_separated: If True and the formula is mixed-typed but already
            separated into type-specific subproblems, use a specialized elimination
            routine for separated mixed forms.

    Returns:
        A new ExtendedFNode where the Ramsey quantifier has been fully eliminated.

    Raises:
        AssertionError: If `f` is not a Ramsey node.
    """

    assert f.is_ramsey(), "Expected a Ramsey formula node."

    # Determine the type of the first quantified variable group
    q1, _ = f.quantifier_vars()

    if all(v.symbol_type().is_real_type() for v in q1):
        typ = _RamseyTypes.REAL
    elif all(v.symbol_type().is_int_type() for v in q1):
        typ = _RamseyTypes.INT
    else:
        typ = _RamseyTypes.MIXED

    # Dispatch to the corresponding elimination algorithm
    match typ:
        case _RamseyTypes.INT:
            # Purely integer variables
            return full_ramsey_elimination_int(f)
        case _RamseyTypes.REAL:
            # Purely real variables
            return full_ramsey_elimination_real(f)
        case _RamseyTypes.MIXED:
            # Mixed integer/real variables
            if is_mixed_separated:
                # If already split by domain, use optimized elimination
                return eliminate_mixed_ramsey_from_separated(f)
            else:
                # Otherwise, apply the general mixed-domain algorithm
                return full_mixed_ramsey_elimination(f)
