import sys
from pathlib import Path

# Add parent directory to path
sys.path.append(str(Path(__file__).parent.parent))

from benchmarks.benchmark_utils import Timer
from ramsey_elimination.formula_utils import int_vector, real_vector
from ramsey_elimination.monadic_decomposition import is_mondec
from ramsey_extensions.shortcuts import *
from ramsey_extensions.environment import push_ramsey

def benchmark_imp_int(dim: int, k: int):
    x = int_vector('x', dim)
    y = int_vector('y', dim)
    f = And([Or(LT(x[i], Int(0)), And(GE(Plus(x[i], y[i]), Int(k)), GE(y[i], Int(0)))) for i in range(dim)])
    return f


def benchmark_imp_real(dim: int, k: int):
    x = real_vector('x', dim)
    y = real_vector('y', dim)
    f = And([
        Or(
            LT(x[i], Real(0)),
            And(
                GE(Plus(x[i], y[i]), Real(k)),
                GE(y[i], Real(0))
            )
        ) for i in range(dim)
    ])
    return f


def benchmark_diagonal_int(dim: int, k: int):
    x = int_vector('x', dim)
    f = And([Equals(x[0], x[i]) for i in range(1, dim)])
    f = And(f, LE(Int(0), x[0]), LE(x[0], Int(k)))
    return f


def benchmark_diagonal_real(dim: int, k: int):
    x = real_vector('x', dim)
    f = And([Equals(x[0], x[i]) for i in range(1, dim)])
    f = And(f, LE(Real(0), x[0]), LE(x[0], Real(k)))
    return f

def benchmark_cubes_int(dim: int, k: int, restrict: bool):
    x = int_vector('x', dim)
    f = Or([
        And([
            And(LE(Int(i), x[j]), LE(x[j], Int(i + 2)))
            for j in range(dim)
        ]) for i in range(k)
    ])
    if restrict:
        f = And(f, LE(Plus(*[x[i] for i in range(dim)]), Int(k)))
    return f


def benchmark_cubes_real(dim: int, k: int, restrict: bool):
    x = real_vector('x', dim)
    f = Or([
        And([
            And(LE(Real(i), x[j]), LE(x[j], Real(i + 2)))
            for j in range(dim)
        ]) for i in range(k)
    ])
    if restrict:
        f = And(f, LE(Plus(*[x[i] for i in range(dim)]), Real(k)))
    return f

def benchmark_mixed(dim: int, l: int, u: int):
    x = int_vector('x', dim)
    y_int = int_vector('y_int', dim)
    y_real = real_vector('y_real', dim)

    f1 = And([Equals(x[i], y_int[i]) for i in range(dim)])
    f2 = And([And(LE(Real(0), y_real[i]), LT(y_real[i], Real(1))) for i in range(dim)])
    f3 = And([LE(Int(l), y_int[i]) for i in range(dim)])
    f4 = And([
        Or(
            LT(y_int[i], Int(u)),
            And(Equals(y_int[i], Int(u)), Equals(y_real[i], Real(0)))
        ) for i in range(dim)
    ])
    return And(f1, f2, f3, f4)

def benchmark_add_real(dim: int):
    x = Symbol("x", REAL)
    y = real_vector("y", dim)

    sy = Plus(*y)
    syp = Plus(sy, Real(1))

    t1 = And(LT(sy, x), LT(x, syp))
    t2 = And(*[
        Or(Equals(y[idx], Real(0)), Equals(y[idx], Real(2**(idx+1))))
        for idx in range(len(y))
    ])

    return And(t1, t2)

def benchmark_sanity_lt():
    x, y = Symbol("x", REAL), Symbol("y", REAL)
    return And(LT(x, Real(1)), LT(y, Real(2)))

def benchmark_sanity_eq():
    x, y, z = Symbol("x", REAL), Symbol("y", REAL), Symbol("z", REAL)
    return And(Equals(x, Real(1)), Equals(y, Real(2)), Equals(z, Real(3)))

if __name__ == "__main__":
    push_ramsey()
    with Timer() as t:
        r = is_mondec(benchmark_add_real(8))
        # r = is_mondec(benchmark_sanity_lt()) #type: ignore
        print(r)
    print(t.interval)

