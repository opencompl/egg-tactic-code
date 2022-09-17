#!/usr/bin/env python3
import os
import subprocess
from pathlib import Path
import logging
from timeit import default_timer as timer
import csv

# Coq proof:
# ---------
# Inductive B := 
# | O | I.
# Theorem count_upward_v3: forall
#     (count: B -> B -> B -> B)
#     (count_0: forall (b2 b1: B), count b2 b1 O = count b2 b1 I)
#     (count_1: forall (b2: B), count b2 O I = count b2 I O)
#     (count_2: count O I I = count I O O), count I I I = count O O O.
# Proof.
#   intros.
#   congruence.
# Qed.
# Set Printing All.
# Print count_upward_v3.

def count_program_coq(n: int):
    out = ""
    out += "Inductive B := O | I.\n"
    out += f"Theorem count_upward_{n}: forall"
    out += f"\n(count: " + ("B ->" * n) + "B" + ")"
    for i in range(1, n+1):
        # [n-1, i): universally quantified
        # [i]: O
        # [i-1, 0): I
        out += f"\n(count_{i}:"
        univ_vars = [f"b{i}" for i in list(range(n, i, -1))]
        if univ_vars:
            out += "forall (" +  " ".join (univ_vars) + ": B), "

        # lhs
        out += "count "
        out += " ".join(univ_vars)
        out += " O"; # i
        out += " I" * ((i - 1) - 0)

        out += " = "

        # lhs
        out += "count "
        out += " ".join(univ_vars)
        out += " I"; # i
        out += " O" * ((i - 1) - 0)

        out += ")" # rule
    out += "\n,  " + "count " + ("I " * n) + " = " + "count " + (" O" * n) + "."
    out += "\nProof. intros. congruence. Qed.\n";
    return out
    

#N : number of bits
# tactic name is (simp|rawEgg)
def count_program_lean(n: int, tactic_name: str): 
    out = """
import EggTactic

inductive B where -- bit
| O : B
| I : B
open B
"""
    out += f"def count_upward_{n}"
    out += f"\n(count: " + ("B ->" * n) + "B" + ")"
    for i in range(1, n+1):
        # [n-1, i): universally quantified
        # [i]: O
        # [i-1, 0): I
        out += f"\n(count_{i}:"
        univ_vars = [f"b{i}" for i in list(range(n, i, -1))]
        if univ_vars:
            out += "∀ (" +  " ".join (univ_vars) + ": B), "

        # lhs
        out += "count "
        out += " ".join(univ_vars)
        out += " O"; # i
        out += " I" * ((i - 1) - 0)

        out += " = "

        # lhs
        out += "count "
        out += " ".join(univ_vars)
        out += " I"; # i
        out += " O" * ((i - 1) - 0)

        out += ")" # rule
    out += "\n  : " + "count " + ("I " * n) + " = " + "count " + (" O" * n)
    out += ":= by {"
    out += tactic_name + "["+ ", ".join([f"count_{i}" for i in range(1, n+1)]) + "]";
    out += "}"
    return out

def find_repo(path):
    "Find repository root from the path's parents"
    for path in Path(path).parents:
        # Check whether "path/.git" exists and is a directory
        git_dir = path / ".git"
        if git_dir.is_dir():
            return path

if __name__ == "__main__":
    logging.basicConfig(level=logging.DEBUG)
    cwd = Path.cwd()
    logging.debug(f"cwd: {cwd}")
    rootdir = find_repo(cwd)
    os.chdir(rootdir)

    logging.debug(f"rootdir: {rootdir}")
    assert rootdir, "Expected to find .git repo from path {path}"

    os.makedirs(cwd / "build" / "lean", exist_ok=True)
    os.makedirs(cwd / "build" / "coq", exist_ok=True)

    data_header = ["tool", "problemsize", "time"]
    N = 8 # failed at max. recursion depth exceeeded at N=9

    with open(cwd / "stats.csv", "w") as OUTFILE:
        writer = csv.writer(OUTFILE)
        writer.writerow(data_header)
        for i in range(1, N+1): # For Andres to count numbers
            logging.debug(f"Generating ({i}/{N})")
            # LEAN runner
            with open(cwd / "build" / "lean" / f"n{i}.lean", "w") as f:
                f.write(count_program_lean(i, "rawEgg"))
            os.environ['LEAN_PATH'] = str(rootdir / "build" / "lib")
            logging.debug("export LEAN_PATH=" + str(rootdir / "build" / "lib"))
            command = ['lean', cwd / "build" / "lean" / f"n{i}.lean"]
            start = timer()
            subprocess.check_call(command)
            end = timer()
            row = ["lean-egg", i, str(end - start)]
            assert len(row) == len(data_header)
            logging.debug(row)
            writer.writerow(row)
            OUTFILE.flush(); os.fsync(OUTFILE)
            # COQ runner
            with open(cwd / "build" / "coq" / f"n{i}.v", "w") as f:
                f.write(count_program_coq(i))
            command = ['coqc', cwd / "build" / "coq" / f"n{i}.v"]
            start = timer()
            subprocess.check_call(command)
            end = timer()
            row = ["coq", i, str(end - start)]
            assert len(row) == len(data_header)
            logging.debug(row)
            writer.writerow(row)
            OUTFILE.flush(); os.fsync(OUTFILE)
