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
    def __init__(self):
        self.start = None
        self.end = None
        self.interval = None
        
    def __enter__(self):
        self.start = time.perf_counter()
        return self
        
    def __exit__(self, exc_type, exc, tb):
        self.end = time.perf_counter()
        self.interval = self.end - self.start

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

def run_benchmark(formula: ExtendedFNode):
    stats = {}
    
    # Measure elimination
    with Timer() as elim_timer, SuspendTypeChecking():
        r = full_ramsey_elimination_int(formula)
    stats['elim_time'] = elim_timer.interval * 1000  # ms
    
    # Record formula metrics
    stats['in_vars'] = get_variables(formula)
    stats['in_atoms'] = get_atoms(formula)
    stats['out_vars'] = get_variables(r)
    stats['out_atoms'] = get_atoms(r)
    
    # Measure solving if enabled
    if ELIMINATE_AND_SOLVE:
        with Timer() as solve_timer:
            sat = is_sat(r)
        stats['solve_time'] = solve_timer.interval * 1000  # ms
        stats['sat'] = sat
    else:
        stats['solve_time'] = None
        stats['sat'] = None
        
    return stats

def format_arg(arg, max_len=20):
    """Format an argument with truncation for long representations"""
    s = str(arg)
    if len(s) > max_len:
        return s[:max_len-3] + '...'
    return s

def format_args(args, max_len=20):
    """Format a tuple of arguments with truncation"""
    if not args:
        return "()"
    return '(' + ', '.join(format_arg(a, max_len) for a in args) + ')'

# Collect all benchmark functions whose names end with '_int'
def get_benchmark_functions(module):
    funcs = []
    for name, obj in inspect.getmembers(module, inspect.isfunction):
        if name.startswith('benchmark_'):
            funcs.append((name, obj))
    return funcs

def format_table_row(values, widths):
    return "| " + " | ".join(f"{str(val):<{widths[i]}}" for i, val in enumerate(values)) + " |"

def format_header_separator(widths):
    return "|-" + "-|-".join("-" * w for w in widths) + "-|"

def run_all_benchmarks(module, arg_map=None):
    bench_funcs = get_benchmark_functions(module)
    results = []
    
    for name, func in bench_funcs:
        if arg_map and name in arg_map:
            arg_sets = arg_map[name]
        else:
            print(f"Skipping {name}: no argument mapping provided.")
            continue
            
        for args in arg_sets:
            if not isinstance(args, tuple):
                args = (args,)
                
            # Format arguments for clean output
            formatted_args = format_args(args)
            print(f"--- Running {name}{formatted_args} ---")
            
            try:
                reset_env()
                formula = func(*args)
                stats = run_benchmark(formula)
                
                # Add benchmark info to stats
                stats['name'] = name
                stats['args'] = formatted_args
                results.append(stats)
                
            except Exception as e:
                print(f"Error in {name}{formatted_args}: {e}")
                continue
                
    # Print summary table
    headers = [
        'Benchmark', 'Arguments', 
        'Elim (ms)', 'Solve (ms)', 
        'SAT', 
        'In Vars', 'In Atoms', 
        'Out Vars', 'Out Atoms'
    ]
    
    # Calculate column widths
    col_widths = [len(h) for h in headers]
    for stats in results:
        values = [
            stats['name'],
            stats['args'],
            f"{stats['elim_time']:.2f}",
            f"{stats['solve_time']:.2f}" if stats['solve_time'] is not None else 'N/A',
            str(stats['sat']) if stats['sat'] is not None else 'N/A',
            str(stats['in_vars']),
            str(stats['in_atoms']),
            str(stats['out_vars']),
            str(stats['out_atoms'])
        ]
        for i, val in enumerate(values):
            col_widths[i] = max(col_widths[i], len(str(val)))
    
    # Add some padding
    col_widths = [w + 2 for w in col_widths]
    
    # Print table header
    print("\n" + "="*80)
    print("BENCHMARK SUMMARY")
    print("="*80)
    print(format_table_row(headers, col_widths))
    print(format_header_separator(col_widths))
    
    # Print table rows
    for stats in results:
        values = [
            stats['name'],
            stats['args'],
            f"{stats['elim_time']:.2f}",
            f"{stats['solve_time']:.2f}" if stats['solve_time'] is not None else 'N/A',
            str(stats['sat']) if stats['sat'] is not None else 'N/A',
            stats['in_vars'],
            stats['in_atoms'],
            stats['out_vars'],
            stats['out_atoms']
        ]
        print(format_table_row(values, col_widths))
    
    print("="*80)
    print(f"Total benchmarks: {len(results)}")
    print("="*80)

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
        #'benchmark_multi_resource_scheduling': [(1000, 998)], # dim=1000, n_resources=998
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
