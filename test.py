from RamseyQuantors.environment import push_ramsey
from RamseyQuantors.shortcuts import *

from RamseyQuantors.integer_elimination import full_ramsey_elimination_int


push_ramsey()

get_env().enable_infix_notation = True


x = Symbol("a", INT)
y = Symbol("b", INT)
f = And(Int(2)*y <= x, x >= Int(5))


def equal_exists_int(dim: int):
    x = [Symbol(f"a_{i}", INT) for i in range(dim)]
    y = [Symbol(f"b_{i}", INT) for i in range(dim)]
    z = [Symbol(f"c_{i}", INT) for i in range(dim)]

    # f = And([And(x[i] < y[i], Equals(x[i], z[i])) for i in range(dim)])
    f = And([And(x[i] < y[i], Equals(x[i], z[i])) for i in range(dim)])
    ef = Exists(z, f)
    ref = Ramsey(x, y, ef)

    return ref

class SuspendTypeChecking(object):
    """Context to disable type-checking during formula creation."""

    def __init__(self, env=None):
        if env is None:
            env = get_env()
        self.env = env
        self.mgr = env.formula_manager

    def __enter__(self):
        """Entering a Context: Disable type-checking."""
        self.mgr._do_type_check = lambda x : x
        return self.env

    def __exit__(self, exc_type, exc_val, exc_tb):
        """Exiting the Context: Re-enable type-checking."""
        self.mgr._do_type_check = self.mgr._do_type_check_real

f = equal_exists_int(1)
#print(f.serialize())
print(full_ramsey_elimination_int(f).serialize())

