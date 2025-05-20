from RamseyQuantors.shortcuts import *
from RamseyQuantors.environment import push_ramsey

from benchmarks.benchmark_utils import benchmark

push_ramsey()
get_env().enable_infix_notation = True


def int_vector(name, dim):
    return [Symbol(f"{name}_{i}", INT) for i in range(dim)]

def benchmark_half_int(dim: int, bound: int):
    x = int_vector("a", dim)
    y = int_vector("b", dim)
    f = And([And(Times(Int(2), y[i]) <= x[i], x[i] >= Int(bound)) for i in range(dim)])
    benchmark(Ramsey(x, y, f))

def benchmark_equal_exists_int(dim: int):
    x = int_vector("a", dim)
    y = int_vector("b", dim)
    z = int_vector("c", dim)

    f = And([And(x[i] < y[i], Equals(x[i], z[i])) for i in range(dim)])

    benchmark(Ramsey(x, y, Exists(z, f)))

def benchmark_equal_exists_2_int(dim: int):
    x = int_vector("a", dim)
    y = int_vector("b", dim)
    z = int_vector("c", dim)

    f = And([And(x[i] < y[i], And(x[i] <= z[i], x[i] >= z[i])) for i in range(dim)])

    benchmark(Ramsey(x, y, Exists(z, f)))

def benchmark_equal_free_int(dim: int):
    x = int_vector("a", dim)
    y = int_vector("b", dim)
    z = int_vector("c", dim)

    f = And([And(x[i] < y[i], Equals(x[i], z[i])) for i in range(dim)])

    benchmark(Ramsey(x, y, f))

def benchmark_equal_free_2_int(dim: int):
    x = int_vector("a", dim)
    y = int_vector("b", dim)
    z = int_vector("c", dim)

    f = And([And(x[i] < y[i], And(x[i] >= z[i], x[i] <= z[i])) for i in range(dim)])

    benchmark(Ramsey(x, y, f))

def benchmark_dickson_int(dim: int):
    x = int_vector("a", dim)
    y = int_vector("b", dim)

    f = And([x[i] >= 0 for i in range(dim)])
    g = And(Or([y[i] < x[i] for i in range(dim)]),And([y[i] <= x[i] for i in range(dim)]))
    g = Or(g,And(Or([y[i] < x[i] for i in range(dim)]),Or([x[i] < y[i] for i in range(dim)])))
    f = And(f,g)

    benchmark(Ramsey(x, y, f))

