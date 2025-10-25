# REAL - Ramsey Elimination in Arithmetic Logics

REAL is a high-performance tool for eliminating Ramsey quantifiers in SMT-LIB formulas, producing standard SMT-LIB output compatible with solvers like Z3 and CVC5. It enables users to work with advanced quantified formulas while remaining within standard SMT-LIB frameworks.

## Features

* **Ramsey Quantifier Elimination**: Efficiently removes `ramsey` quantifiers from SMT-LIB formulas.
* **Linear Elimination**: The elimination algorithm is linear in both output size and runtime.
* **Supported Theories**: Handles Linear Integer Arithmetic (LIA), Linear Real Arithmetic (LRA), and Linear Integer-Real Arithmetic (LIRA).
* **Formula Statistics & Timing**: Optionally provides formula size information and runtime measurements for the elimination process.
* **SMT-LIB Compatibility**: Generates output fully compatible with popular solvers like Z3 and CVC5.

## Extending SMT-LIB

REAL extends SMT-LIB syntax to represent Ramsey quantifiers. Two forms are supported:

```
(ramsey (sorted_var+) (sorted_var+) term)
(ramsey sort (symbol+) (symbol+) term)
```

* The first form allows general Ramsey quantifiers over sorted variables.
* The second form is a shorthand for quantifiers restricted to a single sort (integer or real).

**Example SMT-LIB usage**:

```smt2
(assert (ramsey ((Int x_1) (Real x_2)) ((Int y_1) (Real y_2))
        (and (> x_1 0) (< y_1 10) (< x_2 y_1) (< x_1 y_2))))
(check-sat)
```

This asserts a formula with Ramsey quantification over pairs of integer and real variables.

## Installation

```bash
git clone https://github.com/DarkVanityOfLight/REAL
cd ramsey-elimination
pipenv install
```

## Usage

To run the elimination:

```bash
pipenv shell
python elimination.py <input_file>
```

Replace `<input_file>` with your SMT-LIB file containing Ramsey quantifiers. For a list of available options, run:

```bash
python elimination.py --help
```

## Benchmarking

Benchmarks can be run on different sets of formulas to evaluate performance:

```bash
python benchmark.py <module>
```

Use `--help` to see available modules, output formats, and timing options.

## Architecture

REAL is organized into three main packages:

### Ramsey Extension (`ramsey_extensions`)

* Adds PySMT support for Ramsey quantifiers, modulo operations, and `ToInteger` (floor) operations.
* Provides parsing and serialization of formulas, variable substitution, free-variable analysis, and extended type checking.
* Node definitions are in `operators.py` and `fnode.py`, while walkers and utilities facilitate manipulation of formulas and integration with PySMT.

### Ramsey Quantifier Elimination (`ramsey_elimination`)

* Implements elimination routines for LIA, LRA, and LIRA (which uses both LIA and LRA routines).
* `existential_elimination.py`: Utilities for eliminating existential quantifiers under a Ramsey quantifier.
* `formula_utils.py`: Functions for walking the AST, creating formulas, and representing/manipulating atoms.
* `simplifications.py`: Normalizes atoms and preprocesses formulas for efficient elimination.
* `monadic_decomposition.py`: Checks for monadic decomposability, requiring a compatible PySMT solver.
* `eliminate_ramsey.py`: Top-level interface automatically detects the theory and applies the appropriate elimination routine.

### Benchmarking & Testing

* `benchmark.py` provides scripts and utilities to run benchmarks, measure runtime, and report formula size changes before and after elimination.

## Generated Examples
In combinations with [FASTer](https://tapas.labri.fr/wp/?page_id=23) and [Alchemist](https://github.com/DarkVanityOfLight/alchemist), REAL 
provides an automated pipeline for checking liveness properties of a broad class of integer counter systems,
the `generated` directory, provides several example files of this.

