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
    f = And([And(x[i] < y[i], And(GE(x[i], z[i]), LE(x[i], z[i]))) for i in range(dim)])
    ef = Exists(z, f)
    ref = Ramsey(x, y, ef)

    return ref


f = equal_exists_int(1000)
#print(f.serialize())
full_ramsey_elimination_int(f)

