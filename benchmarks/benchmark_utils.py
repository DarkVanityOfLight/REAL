import sys
import os
import time
import inspect
import argparse
import importlib
import csv

sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

from pysmt.environment import pop_env
from pysmt.shortcuts import is_sat, get_env
from ramsey_extensions.environment import push_ramsey
from ramsey_extensions.fnode import ExtendedFNode

from ramsey_elimination.real_elimination import full_ramsey_elimination_real
from ramsey_elimination.integer_elimination import full_ramsey_elimination_int
from ramsey_elimination.formula_utils import is_atom

# --- Utility Classes and Functions ---

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
    def __init__(self, env=None):
        if env is None:
            env = get_env()
        self.env = env
        self.mgr = env.formula_manager

    def __enter__(self):
        self.mgr._do_type_check = lambda x : x
        return self.env

    def __exit__(self, exc_type, exc_val, exc_tb):
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
        if is_atom(node):
            seen.add(node)
            return
        for arg in node.args():
            walk(arg)

    walk(formula)
    return len(seen)

def reset_env():
    pop_env()
    push_ramsey()
    get_env().enable_infix_notation = True

# --- Core Benchmarking Logic ---

def run_benchmark(formula: ExtendedFNode, elimination_func):
    """Runs elimination and solving for a single formula."""
    stats = {}
    
    with Timer() as elim_timer, SuspendTypeChecking():
        r = elimination_func(formula)
    stats['elim_time'] = elim_timer.interval * 1000

    stats['in_vars'] = get_variables(formula)
    stats['in_atoms'] = get_atoms(formula)
    stats['out_vars'] = get_variables(r)
    stats['out_atoms'] = get_atoms(r)
    
    with Timer() as solve_timer:
        sat = is_sat(r)
    stats['solve_time'] = solve_timer.interval * 1000
    stats['sat'] = sat
        
    return stats

def format_arg(arg, max_len=20):
    s = str(arg)
    return s if len(s) <= max_len else s[:max_len-3] + '...'

def format_args(args, max_len=20):
    return '(' + ', '.join(format_arg(a, max_len) for a in args) + ')'

def get_benchmark_functions(module):
    return [(name, obj) for name, obj in inspect.getmembers(module, inspect.isfunction) if name.startswith('benchmark_')]

def run_all_benchmarks(module, arg_map, elimination_func, title):
    """Runs all benchmarks from a module and outputs results in CSV format."""
    bench_funcs = get_benchmark_functions(module)
    results = []
    
    # Print status updates to stderr to keep stdout clean for CSV data
    print(f"--- Starting {title} ---", file=sys.stderr)
    
    for name, func in bench_funcs:
        if name not in arg_map:
            continue
            
        for args in arg_map[name]:
            if not isinstance(args, tuple):
                args = (args,)
                
            formatted_args = format_args(args)
            print(f"Running {name}{formatted_args}...", file=sys.stderr)
            
            try:
                reset_env()
                formula = func(*args)
                stats = run_benchmark(formula, elimination_func)
                stats['name'] = name.replace('benchmark_', '')
                stats['args'] = formatted_args
                results.append(stats)
            except Exception as e:
                print(f"  ERROR: {e}", file=sys.stderr)
                
    if not results:
        print(f"No benchmarks were successfully run for {title}.", file=sys.stderr)
        return

    # --- CSV Output ---
    headers = ['Benchmark', 'Arguments', 'Elim (ms)', 'Solve (ms)', 'SAT', 'In Vars', 'In Atoms', 'Out Vars', 'Out Atoms']
    
    # Use the csv module to write to standard output
    writer = csv.writer(sys.stdout)
    
    # Write header row
    writer.writerow(headers)
    
    # Write data rows
    for stats in results:
        writer.writerow([
            stats['name'],
            stats['args'],
            f"{stats['elim_time']:.2f}",
            f"{stats['solve_time']:.2f}",
            stats['sat'],
            stats['in_vars'],
            stats['in_atoms'],
            stats['out_vars'],
            stats['out_atoms']
        ])

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description="Run Ramsey elimination benchmarks from a specific module.")
    parser.add_argument("module", help="Name of the benchmark module to run (e.g., 'real_benchmarks' or 'int_benchmarks')")
    cmd_args = parser.parse_args()

    # --- Define Argument Maps ---
    # Argument mapping for REAL benchmarks
    args_map_real = {
        'benchmark_half_real': [(1000, 5.0)],
        'benchmark_equal_exists_real': [(1000,)],
        'benchmark_equal_free_real': [(1000,)],
        'benchmark_dickson_real': [(1000,)],
    }

    args_map_int = {
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

# --- Select Benchmark Suite Based on Command-Line Argument ---
    try:
        # To handle file paths correctly, we'll assume the module is in the current directory
        module_path = cmd_args.module.replace('.py', '')
        benchmark_module = importlib.import_module(module_path)
    except ModuleNotFoundError:
        print(f"Error: Module '{cmd_args.module}' not found in the search path.", file=sys.stderr)
        sys.exit(1)

    # Determine which elimination function and argument map to use
    if 'real' in cmd_args.module:
        elimination_function = full_ramsey_elimination_real
        argument_map = args_map_real
        suite_title = "REAL BENCHMARKS"
    elif 'int' in cmd_args.module:
        elimination_function = full_ramsey_elimination_int
        argument_map = args_map_int
        suite_title = "INTEGER BENCHMARKS"
    else:
        print(f"Error: Cannot determine theory for module '{cmd_args.module}'. Name must contain 'real' or 'int'.", file=sys.stderr)
        sys.exit(1)

    # --- Run the Selected Benchmarks ---
    run_all_benchmarks(
        module=benchmark_module,
        arg_map=argument_map,
        elimination_func=elimination_function,
        title=suite_title
    )
