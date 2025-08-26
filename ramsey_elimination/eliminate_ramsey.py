from enum import Enum, auto
from ramsey_elimination.integer_elimination import full_ramsey_elimination_int
from ramsey_elimination.mixed_elimination import eliminate_mixed_ramsey_from_separated, full_mixed_ramsey_elimination
from ramsey_elimination.real_elimination import full_ramsey_elimination_real
from ramsey_extensions.fnode import ExtendedFNode


class _RamseyTypes(Enum):
    INT = auto()
    REAL = auto()
    MIXED = auto()

def eliminate_ramsey(f: ExtendedFNode, is_mixed_separated=False) -> ExtendedFNode:
    assert f.is_ramsey()

    q1, _ = f.quantifier_vars()
    if all(v.symbol_type().is_real_type() for v in q1): typ = _RamseyTypes.REAL
    elif all(v.symbol_type().is_int_type() for v in q1): typ = _RamseyTypes.INT
    else: typ = _RamseyTypes.MIXED

    match typ:
        case _RamseyTypes.INT:
            return full_ramsey_elimination_int(f)
        case _RamseyTypes.REAL:
            return full_ramsey_elimination_real(f)
        case _RamseyTypes.MIXED:
            if is_mixed_separated:
                return eliminate_mixed_ramsey_from_separated(f)
            else:
                return full_mixed_ramsey_elimination(f)
