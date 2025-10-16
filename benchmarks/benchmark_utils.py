#!/usr/bin/env python3
"""

Usage:
    python benchmark.py real_benchmarks
    python benchmark.py int_benchmarks --format json
    python benchmark.py custom_benchmarks --timeout 30
    python benchmark.py --list-benchmarks int_benchmarks
"""

import sys
import os
import time
import inspect
import argparse
import importlib
import csv
import json
from pathlib import Path
from typing import Dict, List, Tuple, Any, Optional, Callable
from dataclasses import dataclass, asdict

# Add parent directory to path
sys.path.append(str(Path(__file__).parent.parent))

from pysmt.environment import pop_env
from pysmt.shortcuts import is_sat, get_env
from ramsey_extensions.environment import push_ramsey
from ramsey_extensions.fnode import ExtendedFNode

from ramsey_elimination.real_elimination import full_ramsey_elimination_real
from ramsey_elimination.integer_elimination import full_ramsey_elimination_int
from ramsey_elimination.formula_utils import is_atom

# --- Configuration ---

@dataclass
class BenchmarkConfig:
    """Configuration for benchmark execution."""
    timeout_seconds: Optional[float] = None
    max_arg_display_length: int = 50
    output_format: str = 'csv'  # csv, json, table
    verbose: bool = False

@dataclass
class BenchmarkResult:
    """Results from a single benchmark run."""
    name: str
    args: str
    elim_time_ms: float
    solve_time_ms: float
    total_time_ms: float
    is_sat: bool
    input_vars: int
    input_atoms: int
    output_vars: int
    output_atoms: int
    error: Optional[str] = None
    timeout: bool = False

# --- Auto-Discovery System ---

def get_benchmark_functions(module):
    """Extract benchmark functions from a module."""
    return [
        (name, obj) 
        for name, obj in inspect.getmembers(module, inspect.isfunction) 
        if name.startswith('benchmark_')
    ]

def discover_benchmark_config(module) -> Dict[str, Any]:
    """
    Automatically discover benchmark configuration from a module.
    
    The module can define:
    - ELIMINATION_FUNC: The elimination function to use
    - BENCHMARK_ARGS: Dictionary mapping benchmark names to argument lists
    - Or fall back to theory-based detection
    """
    config = {}
    
    # Try to get elimination function from module
    if hasattr(module, 'ELIMINATION_FUNC'):
        config['elimination_func'] = module.ELIMINATION_FUNC
    else:
        # Fall back to theory-based detection
        module_name = module.__name__.lower()
        if 'real' in module_name:
            config['elimination_func'] = full_ramsey_elimination_real
        elif 'int' in module_name:
            config['elimination_func'] = full_ramsey_elimination_int
        else:
            raise ValueError(f"Cannot determine elimination function for module '{module.__name__}'. "
                           "Module name must contain 'real' or 'int', or define ELIMINATION_FUNC.")
    
    # Try to get benchmark arguments from module
    if hasattr(module, 'BENCHMARK_ARGS'):
        config['args'] = module.BENCHMARK_ARGS
    else:
        # Use default arguments based on available functions
        bench_funcs = get_benchmark_functions(module)
        config['args'] = {}
        
        # Auto-generate simple argument sets
        for name, func in bench_funcs:
            # Try to inspect function signature for smart defaults
            sig = inspect.signature(func)
            param_count = len(sig.parameters)
            
            if param_count == 0:
                config['args'][name] = [()]
            elif param_count == 1:
                config['args'][name] = [(1000,)]  # Common dimension
            elif param_count == 2:
                # Try to guess based on function name
                if 'real' in name.lower():
                    config['args'][name] = [(1000, 5.0)]
                else:
                    config['args'][name] = [(1000, 50)]
            else:
                # For complex functions, require explicit configuration
                config['args'][name] = []
                print(f"Warning: {name} has {param_count} parameters. "
                      f"Please define BENCHMARK_ARGS in the module.", file=sys.stderr)
    
    return config

# --- Built-in Configurations (for backward compatibility) ---
D = 100
BUILTIN_CONFIGS = {
    'real_benchmarks': {
        'elimination_func': full_ramsey_elimination_real,
        'args': {
            'benchmark_half_real': [(D, 0.0)],
            'benchmark_equal_exists_real': [(D,)],
            'benchmark_equal_free_real': [(D,)],
            'benchmark_dickson_real': [(D,)],
            'benchmark_sorted_chain_real': [(D,)],
            'benchmark_average_real': [(D,)],
            'benchmark_average_eq_real': [(D,)],
            'benchmark_midpoint_real': [(D,)],
            'benchmark_bounding_box_real': [(D,)],
            'benchmark_cyclic_dependency_real': [(D,)],
        }
    },
    'int_benchmarks': {
        'elimination_func': full_ramsey_elimination_int,
        'args': {
            # Core benchmarks
            'benchmark_half_int': [(D, 50)],
            'benchmark_equal_exists_int': [(D,)],
            'benchmark_equal_exists_2_int': [(D,)],
            'benchmark_equal_free_int': [(D,)],
            'benchmark_equal_free_2_int': [(D,)],
            'benchmark_dickson_int': [(D,)],
            
            # Extended benchmarks
            'benchmark_congruence_mod_m': [(D, 2)],
            'benchmark_sum_even': [(D,)],
            'benchmark_diff_in_kZ': [(D, 3)],
            'benchmark_sum_eq_C': [(2, 0)],
            'benchmark_dot_product_zero': [(D, [1]*D)],
            'benchmark_sum_zero_hyperplane': [(D,)],
            'benchmark_diff_set': [(D, [[0]*D, [10]*D, [-10]*D])],
            'benchmark_scheduling_overlap': [(2,)],
            'benchmark_divisibility_by_k': [(D, 4)],
            'benchmark_affine_progression': [(D, [1]*D)],
            'benchmark_matrix_kernel': [(D, [[1]*D])],
            'benchmark_stabilizer': [(D, [[1] * D] * 1)],
            'benchmark_weighted_sum_eq': [(D, list(range(1, D+1)))],
            'benchmark_equal_first_k': [(D, 3)],
            'benchmark_sum_parity': [(D,)],
            'benchmark_prefix_monotone': [(D,)],
            'benchmark_sum_zero_or_C': [(D, 5)],
            'benchmark_cross_coordinate_eq': [(D,)],
            'benchmark_mixed_sign_pair': [(D,)],
            'benchmark_sorted_chain_int': [(D,)],
            'benchmark_linear_average_int': [(D,)],
            'benchmark_cyclic_dependency_int': [(D,)],
            'benchmark_dynamic_gap_chain_int': [(D,)],
            'benchmark_bounding_box_int': [(D,)],
            'benchmark_linear_average_eq_int': [(D,)],
        }
    }
}

# --- Utility Classes ---

class Timer:
    """Context manager for timing operations."""
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

class TimeoutError(Exception):
    """Raised when an operation times out."""
    pass

class SuspendTypeChecking:
    """Context manager to temporarily disable type checking."""
    def __init__(self, env=None):
        if env is None:
            env = get_env()
        self.env = env
        self.mgr = env.formula_manager

    def __enter__(self):
        self.mgr._do_type_check = lambda x: x
        return self.env

    def __exit__(self, exc_type, exc_val, exc_tb):
        self.mgr._do_type_check = self.mgr._do_type_check_real

# --- Core Functions ---

def get_variables(formula: ExtendedFNode) -> int:
    """Count unique variables in a formula."""
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
    """Count unique atoms in a formula."""
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
    """Reset the PySMT environment."""
    pop_env()
    push_ramsey()
    get_env().enable_infix_notation = True

def format_args(args: Tuple, max_len: int = 50) -> str:
    """Format function arguments for display."""
    def format_single_arg(arg, max_len):
        s = str(arg)
        if len(s) <= max_len:
            return s
        return s[:max_len-3] + '...'
    
    if not args:
        return "()"
    
    formatted = ', '.join(format_single_arg(a, max_len//len(args)) for a in args)
    result = f"({formatted})"
    
    if len(result) > max_len:
        return result[:max_len-3] + '...)'
    return result

def run_single_benchmark(
    func, 
    args: Tuple, 
    elimination_func, 
    config: BenchmarkConfig
) -> BenchmarkResult:
    """Run a single benchmark with timeout and error handling."""
    name = func.__name__.replace('benchmark_', '')
    args_str = format_args(args, config.max_arg_display_length)
    
    if config.verbose:
        print(f"  Running {name}{args_str}...", file=sys.stderr)
    
    try:
        reset_env()
        
        # Generate formula
        with Timer() as gen_timer:
            formula = func(*args)
        
        if config.verbose:
            print(f"    Formula generated in {gen_timer.interval*1000:.2f}ms", file=sys.stderr)
        
        # Run elimination
        with Timer() as elim_timer, SuspendTypeChecking():
            if config.timeout_seconds:
                # Simple timeout - in production, you might want signal-based timeout
                start_time = time.perf_counter()
                result = elimination_func(formula)
                if time.perf_counter() - start_time > config.timeout_seconds:
                    raise TimeoutError("Elimination timed out")
            else:
                result = elimination_func(formula)
        
        # Get formula statistics
        input_vars = get_variables(formula)
        input_atoms = get_atoms(formula)
        output_vars = get_variables(result)
        output_atoms = get_atoms(result)
        
        # Solve the result
        with Timer() as solve_timer:
            if config.timeout_seconds:
                start_time = time.perf_counter()
                is_satisfiable = is_sat(result)
                if time.perf_counter() - start_time > config.timeout_seconds:
                    raise TimeoutError("Solving timed out")
            else:
                is_satisfiable = is_sat(result)
        
        return BenchmarkResult(
            name=name,
            args=args_str,
            elim_time_ms=elim_timer.interval * 1000,
            solve_time_ms=solve_timer.interval * 1000,
            total_time_ms=(elim_timer.interval + solve_timer.interval) * 1000,
            is_sat=is_satisfiable,
            input_vars=input_vars,
            input_atoms=input_atoms,
            output_vars=output_vars,
            output_atoms=output_atoms
        )
        
    except TimeoutError as e:
        return BenchmarkResult(
            name=name,
            args=args_str,
            elim_time_ms=0.0,
            solve_time_ms=0.0,
            total_time_ms=0.0,
            is_sat=False,
            input_vars=0,
            input_atoms=0,
            output_vars=0,
            output_atoms=0,
            timeout=True,
            error=str(e)
        )
    except Exception as e:
        return BenchmarkResult(
            name=name,
            args=args_str,
            elim_time_ms=0.0,
            solve_time_ms=0.0,
            total_time_ms=0.0,
            is_sat=False,
            input_vars=0,
            input_atoms=0,
            output_vars=0,
            output_atoms=0,
            error=str(e)
        )

def get_benchmark_functions(module):
    """Extract benchmark functions from a module."""
    return [
        (name, obj) 
        for name, obj in inspect.getmembers(module, inspect.isfunction) 
        if name.startswith('benchmark_')
    ]

def get_benchmark_config(module_name: str, benchmark_module) -> Dict[str, Any]:
    """Get benchmark configuration, trying built-in configs first, then auto-discovery."""
    # Try built-in configuration first
    if module_name in BUILTIN_CONFIGS:
        return BUILTIN_CONFIGS[module_name]
    
    # Fall back to auto-discovery
    return discover_benchmark_config(benchmark_module)

def list_available_benchmarks(module, config: Dict[str, Any]) -> None:
    """List all available benchmarks in a module."""
    bench_funcs = get_benchmark_functions(module)
    available_args = config['args']
    
    print("Available benchmarks:")
    print("-" * 50)
    
    for name, func in bench_funcs:
        short_name = name.replace('benchmark_', '')
        args_list = available_args.get(name, [])
        
        print(f"  {short_name}")
        if args_list:
            for args in args_list:
                print(f"    Args: {format_args(args if isinstance(args, tuple) else (args,))}")
        else:
            print("    No predefined arguments")
        
        # Show docstring if available
        if func.__doc__:
            doc_lines = func.__doc__.strip().split('\n')
            print(f"    Description: {doc_lines[0]}")
        print()

def output_results(results: List[BenchmarkResult], config: BenchmarkConfig) -> None:
    """Output results in the specified format."""
    if config.output_format == 'json':
        output_json(results)
    elif config.output_format == 'table':
        output_table(results)
    else:  # default to CSV
        output_csv(results)

def output_csv(results: List[BenchmarkResult]) -> None:
    """Output results in CSV format."""
    if not results:
        return
    
    writer = csv.writer(sys.stdout)
    writer.writerow([
        'Benchmark', 'Arguments', 'Elim (ms)', 'Solve (ms)', 'Total (ms)',
        'SAT', 'In Vars', 'In Atoms', 'Out Vars', 'Out Atoms', 'Error', 'Timeout'
    ])
    
    for result in results:
        writer.writerow([
            result.name,
            result.args,
            f"{result.elim_time_ms:.2f}",
            f"{result.solve_time_ms:.2f}",
            f"{result.total_time_ms:.2f}",
            result.is_sat,
            result.input_vars,
            result.input_atoms,
            result.output_vars,
            result.output_atoms,
            result.error or '',
            result.timeout
        ])

def output_json(results: List[BenchmarkResult]) -> None:
    """Output results in JSON format."""
    json_results = [asdict(result) for result in results]
    print(json.dumps(json_results, indent=2))

def output_table(results: List[BenchmarkResult]) -> None:
    """Output results in a formatted table."""
    if not results:
        print("No results to display.")
        return
    
    # Calculate column widths
    name_width = max(len(r.name) for r in results) + 2
    args_width = min(max(len(r.args) for r in results) + 2, 30)
    
    # Header
    print(f"{'Benchmark':<{name_width}} {'Args':<{args_width}} {'Elim(ms)':>10} {'Solve(ms)':>10} {'Total(ms)':>10} {'SAT':>5} {'Status':<10}")
    print("-" * (name_width + args_width + 55))
    
    # Data rows
    for result in results:
        args_display = result.args[:args_width-3] + "..." if len(result.args) > args_width else result.args
        status = "TIMEOUT" if result.timeout else "ERROR" if result.error else "OK"
        
        print(f"{result.name:<{name_width}} {args_display:<{args_width}} "
              f"{result.elim_time_ms:>10.2f} {result.solve_time_ms:>10.2f} "
              f"{result.total_time_ms:>10.2f} {result.is_sat!s:>5} {status:<10}")

def run_benchmarks(module_name: str, config: BenchmarkConfig, benchmark_name: str | None = None) -> List[BenchmarkResult]:
    """Run benchmarks for a given module, optionally a single benchmark."""
    # Import the benchmark module
    try:
        module_path = module_name.replace('.py', '')
        benchmark_module = importlib.import_module(module_path)
    except ModuleNotFoundError:
        raise ImportError(f"Module '{module_name}' not found in the search path.")
    
    # Get benchmark configuration
    bench_config = get_benchmark_config(module_name, benchmark_module)
    
    # Get benchmark functions
    bench_funcs = get_benchmark_functions(benchmark_module)
    
    if benchmark_name:
        bench_funcs = [bf for bf in bench_funcs if bf[0] == benchmark_name]
        if not bench_funcs:
            print(f"No benchmark named '{benchmark_name}' found in '{module_name}'", file=sys.stderr)
            return []

    if not bench_funcs:
        print(f"No benchmark functions found in '{module_name}'", file=sys.stderr)
        return []
    
    elimination_func = bench_config['elimination_func']
    arg_map = bench_config['args']
    
    results = []
    total_benchmarks = sum(len(arg_map.get(name, [()])) for name, _ in bench_funcs)
    current = 0
    
    print(f"Running {total_benchmarks} benchmark configurations...", file=sys.stderr)
    
    for name, func in bench_funcs:
        args_list = arg_map.get(name, [()])
        
        for args in args_list:
            current += 1
            if not isinstance(args, tuple):
                args = (args,)
            
            if config.verbose:
                print(f"[{current}/{total_benchmarks}]", file=sys.stderr)
            
            result = run_single_benchmark(func, args, elimination_func, config)
            results.append(result)
    
    return results

def main():
    """Main entry point."""
    parser = argparse.ArgumentParser(
        description="Run Ramsey elimination benchmarks",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__
    )
    
    parser.add_argument(
        "module", 
        help="Benchmark module name (e.g., 'real_benchmarks', 'int_benchmarks', 'my_custom_benchmarks')"
    )
    parser.add_argument(
        "--format", 
        choices=['csv', 'json', 'table'], 
        default='csv',
        help="Output format (default: csv)"
    )
    parser.add_argument(
        "--timeout", 
        type=float,
        help="Timeout in seconds for each benchmark"
    )
    parser.add_argument(
        "--verbose", "-v", 
        action='store_true',
        help="Verbose output"
    )
    parser.add_argument(
        "--list-benchmarks", 
        action='store_true',
        help="List available benchmarks and exit"
    )
    parser.add_argument(
        "--max-arg-length", 
        type=int, 
        default=50,
        help="Maximum length for argument display (default: 50)"
    )

    parser.add_argument(
        "--benchmark",
        help="Name of a single benchmark to run (default: run all benchmarks)"
    )
    
    args = parser.parse_args()
    
    config = BenchmarkConfig(
        timeout_seconds=args.timeout,
        max_arg_display_length=args.max_arg_length,
        output_format=args.format,
        verbose=args.verbose
    )
    
    try:
        # Import module
        module_path = args.module.replace('.py', '')
        benchmark_module = importlib.import_module(module_path)
        
        if args.list_benchmarks:
            bench_config = get_benchmark_config(args.module, benchmark_module)
            list_available_benchmarks(benchmark_module, bench_config)
            return
        
        # Run benchmarks
        if args.benchmark:
            results = run_benchmarks(args.module, config, benchmark_name=args.benchmark)
        else:
            results = run_benchmarks(args.module, config)
        
        # Output results
        if results:
            output_results(results, config)
            if config.verbose:
                successful = sum(1 for r in results if not r.error and not r.timeout)
                print(f"\nCompleted: {successful}/{len(results)} successful", file=sys.stderr)
        else:
            print("No benchmarks were run.", file=sys.stderr)
            
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)

if __name__ == '__main__':
    main()
