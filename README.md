# Ramsey Elimination Tool

A high-performance tool for eliminating Ramsey quantifiers in SMT-LIB formulas, producing standard SMT-LIB output compatible with solvers like Z3 and CVC5.

## Features

* **Ramsey Quantifier Elimination**: Efficiently removes `Ramsey` quantifiers from SMT-LIB formulas.
* **Linear Elimination**: The elimination process is linear in both output size and runtime. 
* **Supported Theories**: Handles Linear Integer Arithmetic (LIA), Linear Real Arithmetic (LRA), and Linear Integer-Real Arithmetic (LIRA).
* **Formula Statistics**: Optionally prints formula sizes before and after elimination.
* **Timing Support**: Optionally measures elimination runtime.

## Extending SMT-LIB

Since our goal is to take SMT-LIB input and produce SMT-LIB output, we extend SMT-LIB syntax to express the new Ramsey quantifier. Following SMT-LIB conventions, we define:

```
term ::= ... 
       | (ramsey (sorted_var+) (sorted_var+) term)
       | (ramsey sort (symbol+) (symbol+) term)


The first form `(ramsey (sorted_var+) (sorted_var+) term)` allows general Ramsey quantifiers over sorted variables.
The second form `(ramsey sort (symbol+) (symbol+) term)` is a shorthand for integer-only or real-only quantifiers.

### Example SMT-LIB Snippet

```smt2
(assert (ramsey ((Int x_1) (Real x_2)) ((Int y_1) (Real y_2)) (and (> x_1 0) (< y_1 10) (< x_2 y_1) (< x_1 y_2))))
(check-sat)
```

## Installation

```bash
git clone https://github.com/DarkVanityOfLight/ramsey-linear-arithmetics
cd ramsey-elimination
pipenv install
```

## Usage

```bash
pipenv shell
python elimination.py <input_file> [options]
```

**Arguments**:

* `<input_file>`: Path to the input SMT-LIB (`.smt2`) file containing Ramsey quantifiers.

**Options**:

* `--time` or `-t`: Measure and display the time taken for elimination.
* `--size` or `-s`: Print the formula size before and after elimination.

**Example**:

```bash
python main.py example.smt2 -t -s
```

## Benchmarking

Run benchmarks on different sets of formulas:

```bash
python benchmark.py <module> [options]
```

**Arguments**:

* `<module>`: Benchmark module name (e.g., `real_benchmarks`, `int_benchmarks`, `my_custom_benchmarks`).

**Options**:

* `--format`: Output format (`csv`, `json`, or `table`; default: `csv`).
* `--timeout`: Timeout in seconds for each benchmark.
* `--verbose` or `-v`: Enable verbose output.
* `--list-benchmarks`: List available benchmarks and exit.
* `--max-arg-length`: Maximum length for argument display (default: 50).

**Example**:

```bash
python benchmark.py real_benchmarks --format table --timeout 10 -v
```

This will run the `real_benchmarks` module, print verbose output in table format, and timeout any single benchmark after 10 seconds.
