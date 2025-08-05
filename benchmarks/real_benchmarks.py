
from pysmt.shortcuts import And, Equals, Exists, Or
from ramsey_elimination.formula_utils import real_vector
from ramsey_extensions.shortcuts import Ramsey


def benchmark_half_real(dim: int, bound: float):
    x = real_vector('a',dim)
    y = real_vector('b',dim)
    f = And([And(2*y[i] <= x[i],x[i] >= bound) for i in range(dim)])
    return Ramsey(x, y, f)

def benchmark_equal_exists_real(dim: int):
    x = real_vector('a', dim)
    y = real_vector('b', dim)
    z = real_vector('c', dim)
    f = And([And(x[i] < y[i], Equals(x[i], z[i])) for i in range(dim)])
    return Ramsey(x, y, Exists(z, f))


def benchmark_equal_free_real(dim: int):
    x = real_vector('a', dim)
    y = real_vector('b', dim)
    z = real_vector('c', dim)
    f = And([And(x[i] < y[i], Equals(x[i], z[i])) for i in range(dim)])
    return Ramsey(x, y, f)


def benchmark_dickson_real(dim: int):
    x = real_vector('a', dim)
    y = real_vector('b', dim)
    f = And([x[i] >= 0 for i in range(dim)])
    g = And(Or([y[i] < x[i] for i in range(dim)]),And([y[i] <= x[i] for i in range(dim)]))
    g = Or(g,And(Or([y[i] < x[i] for i in range(dim)]),Or([x[i] < y[i] for i in range(dim)])))
    f = And(f,g)
    return Ramsey(x, y, f)

