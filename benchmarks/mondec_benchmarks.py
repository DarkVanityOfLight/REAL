import sys
from pathlib import Path

from pysmt.environment import pop_env

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



if __name__ == "__main__":
    import csv
    import time

    configs = {
        "imp_int":       [(4,1), (8,2), (16,4), (32,8)],
        "imp_real":      [(4,1), (8,2), (16,4), (32,8)],
        "diagonal_int":  [(8,1), (16,3), (32,5), (64,10)],
        "diagonal_real": [(8,1), (16,3), (32,5), (64,10)],
        "cubes_int":     [(3,4,False), (4,6,False), (6,8,False), (3,4,True), (4,6,True), (6,8,True)],
        "cubes_real":    [(3,4,False), (4,6,False), (6,8,False), (3,4,True), (4,6,True), (6,8,True)],
        # "mixed":         [(4,0,1), (8,0,2), (12,1,3)],
        "add_real":      [4, 8, 16, 20]
    }

    benchmarks = {
        "imp_int": benchmark_imp_int,
        "imp_real": benchmark_imp_real,
        "diagonal_int": benchmark_diagonal_int,
        "diagonal_real": benchmark_diagonal_real,
        "cubes_int": benchmark_cubes_int,
        "cubes_real": benchmark_cubes_real,
        # "mixed": benchmark_mixed,
        "add_real": benchmark_add_real
    }

    with open("benchmark_results.csv", "w", newline="") as csvfile:
        writer = csv.writer(csvfile)
        writer.writerow(["benchmark", "config", "monadically_decomposable", "time_seconds"])
        
        for name, conf_list in configs.items():
            pop_env()
            push_ramsey()
            func = benchmarks[name]
            for conf in conf_list:
                # Construct formula
                if isinstance(conf, tuple):
                    f = func(*conf)
                else:
                    f = func(conf)
                
                # Check monadic decomposability and time it
                start_time = time.time()
                mondec = is_mondec(f)
                elapsed = time.time() - start_time
                
                # Write to CSV
                writer.writerow([name, str(conf), mondec, elapsed])
                print(f"{name} {conf} -> mondec: {mondec}, time: {elapsed:.4f}s")
