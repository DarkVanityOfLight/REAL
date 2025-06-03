import sys, os
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

from pysmt.constants import z3
from pysmt.environment import pop_env
from pysmt.logics import LIA

from RamseyQuantors.environment import push_ramsey
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

def reset_env():
    pop_env()
    push_ramsey()
    get_env().enable_infix_notation = True

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

def format_arg(arg, max_len=50):
    """Format an argument with truncation for long representations"""
    s = str(arg)
    if len(s) > max_len:
        return s[:max_len-3] + '...'
    return s

def format_args(args, max_len=50):
    """Format a tuple of arguments with truncation"""
    return '(' + ', '.join(format_arg(a, max_len) for a in args) + ')'

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
        reset_env()
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
                
            # Format arguments for clean output
            formatted_args = format_args(args)
            print(f"--- Running {name}{formatted_args} ---")
            
            try:
                func(*args)
            except Exception as e:
                print(f"Error in {name}{formatted_args}: {e}")
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
        # Original benchmarks
        'benchmark_half_int': [(1000, 50)],
        'benchmark_equal_exists_int': [(1000,)],
        'benchmark_equal_exists_2_int': [(1000,)],
        'benchmark_equal_free_int': [(1000,)],
        'benchmark_equal_free_2_int': [(1000,)],
        'benchmark_dickson_int': [(1000,)],
        
        # New benchmarks
        'benchmark_congruence_mod_m': [(1000, 2)],          # dim=1000, modulus=2
        'benchmark_sum_even': [(1000,)],                     # dim=1000
        'benchmark_diff_in_kZ': [(1000, 3)],                 # dim=1000, k=3
        'benchmark_sum_eq_C': [(2, 0)],                      # Fixed dim=2, C=0
        'benchmark_dot_product_zero': [(1000, [1]*1000)],     # dim=1000, v=all-ones
        'benchmark_sum_zero_hyperplane': [(1000,)],           # dim=1000
        'benchmark_diff_set': [(1000, [(0,)*1000, (1,)+(0,)*999])],  # dim=1000, D={0, e1}
        'benchmark_scheduling_overlap': [(2,)],              # Fixed dim=2
        'benchmark_multi_resource_scheduling': [(1000, 998)], # dim=1000, n_resources=998
        'benchmark_divisibility_by_k': [(1000, 4)],          # dim=1000, k=4
        'benchmark_affine_progression': [(1000, [1]*1000)],   # dim=1000, v=all-ones
        'benchmark_matrix_kernel': [(1000, [[1]*1000])],      # dim=1000, A=all-ones row
        'benchmark_stabilizer': [(1000, [[1] * 1000] * 1000)],         # dim=1000, M=all-ones row
        'benchmark_weighted_sum_eq': [(1000, list(range(1,1001)))],  # weights=1..1000
        'benchmark_equal_first_k': [(1000, 3)],              # dim=1000, k=3
        'benchmark_sum_parity': [(1000,)],                   # dim=1000
        'benchmark_prefix_monotone': [(1000,)],              # dim=1000
        'benchmark_sum_zero_or_C': [(1000, 5)],              # dim=1000, C=5
        'benchmark_cross_coordinate_eq': [(1000,)],          # dim=1000
        'benchmark_mixed_sign_pair': [(1000,)]               # dim=1000 (n=500 pairs)
    }

    ELIMINATE_AND_SOLVE = True

    run_all_benchmarks(benchmark_module, args_map)
