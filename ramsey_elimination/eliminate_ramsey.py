from pysmt.typing import INT
from ramsey_elimination.integer_elimination import eliminate_ramsey_int
from ramsey_elimination.mixed_elimination import eliminate_ramsey_mixed
from ramsey_elimination.real_elimination import eliminate_ramsey_real
from ramsey_extensions.fnode import ExtendedFNode


def eliminate_ramsey(f: ExtendedFNode) -> ExtendedFNode:
    assert f.is_ramsey()

    if f.arg(0).is_ramsey():
        return eliminate_ramsey_mixed(f)
    elif f.quantifier_vars()[0][0].symbol_type() == INT:
        return eliminate_ramsey_int(f)
    else:
        return eliminate_ramsey_real(f)

