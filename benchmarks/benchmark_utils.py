
import sys, os

from pysmt.constants import z3
from pysmt.logics import LIA
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))
import time
import inspect
import argparse
import importlib

from pysmt.shortcuts import Portfolio, Solver, get_env, get_model, get_unsat_core, is_sat
from pysmt.solvers.z3 import Z3Solver

from RamseyQuantors.fnode import ExtendedFNode
from RamseyQuantors.integer_elimination import full_ramsey_elimination_int
from RamseyQuantors.formula_utils import isAtom

global ELIMINATE_AND_SOLVE
ELIMINATE_AND_SOLVE = True

class Timer:
    def __init__(self, label: str):
        self.label = label
    def __enter__(self):
        self.start = time.perf_counter()
    def __exit__(self, exc_type, exc, tb):
        elapsed = time.perf_counter() - self.start
        print(f"[{self.label}] {elapsed*1000:.2f} ms")

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


def get_variables(formula: ExtendedFNode) -> int:
    seen = set()

    def walk(node):
        if node.is_symbol():
            seen.add(node)
            return

        for arg in node.args():
            walk(arg)

    walk(formula)
    return len(seen)

def get_atoms(formula: ExtendedFNode) -> int:
    seen = set()

    def walk(node):
        if isAtom(node):
            seen.add(node)
            return
        for arg in node.args():
            walk(arg)

    walk(formula)
    return len(seen)

def benchmark(formula: ExtendedFNode):
    with SuspendTypeChecking():
        with Timer("Time elimination: "):
            r = full_ramsey_elimination_int(formula)

    print(f"#Variables input: {get_variables(formula)}")
    print(f"#Atoms input: {get_atoms(formula)}")
    print(f"#Variables output: {get_variables(r)}")
    print(f"#Atoms output: {get_atoms(r)}")


    if ELIMINATE_AND_SOLVE:
        with Timer("Solving: "):
            sat = is_sat(r)
            print(sat)



# Collect all benchmark functions whose names end with '_int'
def get_benchmark_functions(module):
    funcs = []
    for name, obj in inspect.getmembers(module, inspect.isfunction):
        if name.startswith('benchmark_'):
            funcs.append((name, obj))
    return funcs

def run_all_benchmarks(module, arg_map=None):
    bench_funcs = get_benchmark_functions(module)

    for name, func in bench_funcs:
        sig = inspect.signature(func)
        arg_sets = []

        if arg_map and name in arg_map:
            arg_sets = arg_map[name]
        else:
            print(f"Skipping {name}: requires {len(sig.parameters)} args but no mapping provided.")
            continue

        for args in arg_sets:
            if not isinstance(args, tuple):
                args = (args,)
            print(f"--- Running {name} with args={args} ---")
            try:
                func(*args)
            except Exception as e:
                print(f"Error in {name}{args}: {e}")
                continue

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description="Run int benchmarks from a given module.")
    parser.add_argument("module", help="Module name containing benchmark functions (e.g. int_benchmarks)")
    args = parser.parse_args()


    try:
        benchmark_module = importlib.import_module(args.module)
    except ModuleNotFoundError:
        print(f"Error: Module '{args.module}' not found.")
        sys.exit(1)

    # Example argument mapping
    args_map = {
        'benchmark_half_int': [(1000, 50)],
        'benchmark_equal_exists_int': [(1000,)],
        'benchmark_equal_exists_2_int': [(1000,)],
        'benchmark_equal_free_int': [(1000,)],
        'benchmark_equal_free_2_int': [(1000,)],
        'benchmark_dickson_int': [(1000,)],
    }

    ELIMINATE_AND_SOLVE = True

    run_all_benchmarks(benchmark_module, args_map)
