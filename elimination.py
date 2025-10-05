import sys, time
from pathlib import Path
from ramsey_extensions.environment import push_ramsey
from ramsey_extensions.shortcuts import *
from ramsey_elimination.integer_elimination import full_ramsey_elimination_int

push_ramsey()

if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(
        description="Eliminate Ramsey quantifiers and output a new SMT2 file."
    )
    parser.add_argument("input_file", help="Path to the input .smt2 file")
    parser.add_argument("--time", "-t", action="store_true", help="Measure elimination time")
    parser.add_argument("--size", "-s", action="store_true", help="Print formula size before and after elimination")

    args = parser.parse_args()
    input_path = Path(args.input_file)

    if not input_path.exists():
        print(f"Error: File '{input_path}' does not exist.")
        sys.exit(1)

    formula = read_smtlib(str(input_path))

    if args.size:
        pre_size = formula.size()
        print(f"[size:pre] {pre_size}")

    start = time.perf_counter() if args.time else None
    eliminated = full_ramsey_elimination_int(formula)
    elapsed = time.perf_counter() - start if args.time else None

    if args.time:
        print(f"[time] {elapsed:.3f}s")

    if args.size:
        post_size = eliminated.size()
        print(f"[size:post] {post_size}")

    str_elim = to_smtlib(eliminated, False)

    output_path = input_path.with_suffix("")
    output_file = output_path.with_name(f"{output_path.name}_elim.smt2")

    with output_file.open("w", encoding="utf-8") as f:
        f.write(f"(assert {str_elim})\n(check-sat)")

    print(f"Wrote eliminated formula to '{output_file}'")
