#!/usr/bin/env python3

from os import path
import math
import re
import subprocess
import sys
import tempfile
import time


def coq_B(f):
    print("Inductive B := I | O.", file=f)


def lean_B(f):
    print("inductive B", file=f)
    print("| I | O", file=f)
    print("open B", file=f)


def count_sig(N, f):
    args = ["B"] * N
    args.append("B")  # return type
    arg_s = " -> ".join(args)
    print(f"(count: {arg_s})", file=f)


def count_lemma(N, n, f):
    free_vars = []
    for i in reversed(range(n + 1, N + 1)):
        free_vars.append(f"b{i}")
    if free_vars:
        params = "forall {},".format(" ".join(free_vars))
    else:
        params = ""
    args_l = " ".join(free_vars)
    args_r = " ".join(free_vars)
    # we have n arguments left
    args_l += " O" + " I" * (n - 1)
    args_r += " I" + " O" * (n - 1)
    print(f"(count_{n} : {params}", file=f)
    print(f"    count {args_l} = count {args_r})", file=f)


def hint_rewrite(N, f):
    count_lemmas = [f"count_{n}" for n in range(1, N + 1)]
    print("#[local] Hint Rewrite {} : count.".format(" ".join(count_lemmas)), file=f)


def theorem_statement(rewrites, N, f):
    # strip the leading "0b" from the binary representation
    bin_num = bin(rewrites)[2:]
    if len(bin_num) < N:
        bin_num = "0" * (N - len(bin_num)) + bin_num
    count_args = bin_num.replace("0", "O ").replace("1", "I ")
    print("  count {} = count {}".format(count_args, "O " * N), file=f, end="")


def coq_theorem(rewrites, N, f):
    print(f"(* {rewrites} rewrites *)", file=f)
    print("Theorem count_upward :", file=f)
    theorem_statement(rewrites, N, f)
    print(".", file=f)


def coq_proof(rewrites, N, proof, f):
    print("Proof.", file=f)
    print(f'  idtac "rewrites = {rewrites}".', file=f)
    if proof == "congruence":
        for n in range(1, N + 1):
            print(f"pose proof count_{n}.", file=f)
        # This number is the number of quantified hypotheses that can be added
        # to the goal. The default is 1000, which we increase here. Without this
        # parameter congruence would simply fail at some earlier point, but we
        # want to measure its performance a bit further.
        print('time "congruence" congruence 2000.', file=f)
    elif proof == "autorewrite":
        print('  time "autorewrite" autorewrite with count. reflexivity.', file=f)
    print("Qed.", file=f)


def lean_proof(N, f):
    print("begin", file=f)
    count_lemmas = ", ".join([f"count_{n}" for n in range(1, N + 1)])
    print(f"  simp [{count_lemmas}],", file=f)
    print("end", file=f)


def num_digits(rewrites):
    """Compute the number of digits required to represent a number of
    rewrites."""
    return int(math.floor(math.log(rewrites, 2))) + 1


def coq_file(args, f):
    rewrites = args.rewrites
    N = num_digits(rewrites)
    coq_B(f)
    print("Context", file=f)
    print(f"(* N = {N} *)", file=f)
    count_sig(N, f)
    for n in range(1, N + 1):
        count_lemma(N, n, f)
    print(".", file=f)
    print(file=f)
    hint_rewrite(N, f)
    print(file=f)
    coq_theorem(rewrites, N, f)
    coq_proof(rewrites, N, args.proof, f)


def lean_file(args, f):
    rewrites = args.rewrites
    N = num_digits(rewrites)
    lean_B(f)
    print(file=f)
    print("theorem count_upward", file=f)
    count_sig(N, f)
    for n in range(1, N + 1):
        count_lemma(N, n, f)
    print(f" -- rewrites = {rewrites}", file=f)
    print("  :", end="", file=f)
    theorem_statement(rewrites, N, f)
    print(":=", file=f)
    lean_proof(N, f)


def run_coqc(f):
    out = subprocess.run(["coqc", f], capture_output=True)
    if out.returncode != 0:
        if re.search("Tactic failure", out.stderr.decode("utf-8")):
            return None
        else:
            # something else seems to have gone wrong
            print(out.stderr, file=sys.stderr)
            print("Coq failed", file=sys.stderr)
            sys.exit(1)
    return out.stdout.decode("utf-8")


def time_coqc(args, time_complete=True):
    """Time running coqc on a file generated from args.

    If time_complete is True, then time the entire run rather than just the
    autorewrite/congruence invocation. This includes the kernel checking the
    resulting proof.
    """
    with tempfile.TemporaryDirectory() as tempd:
        fname = path.join(tempd, "count.v")
        with open(fname, "w") as f:
            coq_file(args, f)
        start = time.time()
        output = run_coqc(fname)
        if output is None:
            return float("inf")
        elapsed = time.time() - start
        if not time_complete:
            # replace elapsed with the tactic timing result (from the Coq output)
            m = re.search(r"""ran for (?P<time>[0-9.]+) secs""", output)
            if not m:
                print(output)
                print("could not parse Coq output", file=sys.stderr)
                sys.exit(1)
            elapsed = float(m.group("time"))
        return elapsed


def run_and_time_lean(f):
    """Run Lean on a file and return the time elapsed.

    Returns infinity if Lean fails.
    """
    start = time.time()
    # give a higher thread stack size to handle slightly bigger problems
    out = subprocess.run(["lean", "--tstack=50000", f], capture_output=True)
    if out.returncode != 0:
        print(out.stdout.decode("utf-8"), file=sys.stderr)
        return float("inf")
    elapsed = time.time() - start
    return elapsed


def time_lean(args):
    with tempfile.TemporaryDirectory() as tempd:
        fname = path.join(tempd, "count.lean")
        with open(fname, "w") as f:
            lean_file(args, f)
        return run_and_time_lean(fname)


def main():
    import argparse

    parser = argparse.ArgumentParser()
    parser.add_argument("rewrites", type=int)
    parser.add_argument("-o", "--output")
    parser.add_argument(
        "-t", "--time", action="store_true", help="time running theorem prover"
    )
    parser.add_argument(
        "--proof",
        help="choose autorewrite or congruence for Coq, or simp for Lean3",
        default="autorewrite",
    )

    args = parser.parse_args()

    if args.proof not in ["autorewrite", "congruence", "simp"]:
        print("unexpected proof (choose autorewrite|congruence|simp)", file=sys.stderr)
        sys.exit(1)
    if args.proof in ["autorewrite", "congruence"]:
        prover = "coq"
    elif args.proof in ["simp"]:
        prover = "lean"

    if args.output is None or args.output == "-":
        args.output = sys.stdout
    else:
        if "." not in args.output:
            ext = "v" if prover == "coq" else "lean"
            args.output = f"{args.output}.{ext}"
        args.output = open(args.output, "w")

    if not args.time:
        if prover == "coq":
            coq_file(args, args.output)
        elif prover == "lean":
            lean_file(args, args.output)
        return

    # timing
    if prover == "coq":
        t = time_coqc(args)
    elif prover == "lean":
        t = time_lean(args)
    print(f"{args.rewrites}|{args.proof}|{t}")


if __name__ == "__main__":
    main()
