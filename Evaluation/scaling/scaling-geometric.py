#!/usr/bin/env python3
# NOTE: this is a different file from scaling-exponential.py,
# because it does not seem like refactoring the code of scaling-exponential.py
# is worth it initially. If we want more scaling results, we can then
# integrate the codebases.
import os
import subprocess
from pathlib import Path
import logging
from timeit import default_timer as timer
import csv
import shutil
import argparse
import pandas as pd # yeesh
import matplotlib
import numpy as np

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


def num_to_IO(n: int, ndigits: int):
    assert n <= (2 ** ndigits - 1)
    """
    Convert a number into a list of the form ["I", "O"], with most significant bit first.

    eg: (ndigits=5)
    1 -> ["O", "O", "O", "O", "I"]
    2 -> ["O", "O", "O", "I", "O"]
    4 -> ["O", "O", "I", "O", "O"]
    5 -> ["O", "O", "I", "O", "I"]
    """
    out = []
    while n > 0:
        if n % 2 == 0:
            out.append("O")
        else:
            out.append("I")
        n = n // 2
    
    assert len(out) <= ndigits
    # pad with O's
    out = out + ["O"] * (ndigits - len(out))
    out.reverse()
    assert len(out) == ndigits
    return out


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
    out += "\n,  " + "count " + " ".join(num_to_IO(min(2**n-1, n*n), ndigits=n)) + " = " + "count " + " ".join(num_to_IO(0, ndigits=n)) + "."
    out += "\nProof. intros. congruence. Qed.\n";
    return out
    

#N : number of bits
# tactic name is (simp|eggxplosion)
def count_program_lean(n: int, tactic_name: str):
    out = """
import EggTactic
set_option maxRecDepth 20000

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
    # 2^3 - 1 = 7 < 3*3 = 9
    # so we need to "clip" at exponential for small values.
    out += "\n  : " + "count " + " ".join(num_to_IO(min((2**n) - 1, n*n), ndigits=n)) + " = " + "count " + " ".join(num_to_IO(0, ndigits=n))
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

G_DATA_HEADER = ["tool", "problemsize", "time"]

def G_STATS_FILENAME():
    filename = os.path.basename(__file__).replace(".py", ".csv")
    return filename

def run(logging, cwd, rootdir):
    logging.debug("removing directory '" + str(cwd / "build") + "'")
    if (cwd / "build").exists(): shutil.rmtree(cwd / "build")
    logging.debug("making test dirs")
    os.makedirs(cwd / "build" / "lean-egg", exist_ok=True)
    os.makedirs(cwd / "build" / "lean-simp", exist_ok=True)
    os.makedirs(cwd / "build" / "coq", exist_ok=True)

    logging.debug("lake build")
    command = ['lake', 'build']

    N = 15 # failed at max. recursion depth exceeeded at N=9

    with open(cwd / G_STATS_FILENAME(), "w") as OUTFILE:
        writer = csv.writer(OUTFILE)
        writer.writerow(G_DATA_HEADER)
        for i in range(1, N+1): # For Andres to count numbers (thanks <3!)
            logging.debug(f"Generating ({i}/{N})")
            # LEAN egg runner
            testpath = cwd / "build" / "lean-egg" / f"n{i}.lean"
            with open(testpath, "w") as f:
                f.write(count_program_lean(i, "eggxplosion"))
            os.environ['LEAN_PATH'] = str(rootdir / "build" / "lib")
            logging.debug("export LEAN_PATH=" + str(rootdir / "build" / "lib"))
            command = ['lean', testpath]
            start = timer()
            try:
              subprocess.check_call(command)
              end = timer()
              row = ["lean-egg", i, str(end - start)]
            except:
              row = ["lean-egg", i, "ERR"]
            assert len(row) == len(G_DATA_HEADER)
            logging.debug(row)
            writer.writerow(row)
            OUTFILE.flush(); os.fsync(OUTFILE)
            # LEAN simp runner
            testpath = cwd / "build" / "lean-simp" / f"n{i}.lean"
            with open(testpath, "w") as f:
                f.write(count_program_lean(i, "simp"))
            os.environ['LEAN_PATH'] = str(rootdir / "build" / "lib")
            logging.debug("export LEAN_PATH=" + str(rootdir / "build" / "lib"))
            command = ['lean', testpath]
            start = timer()
            try:
              subprocess.check_call(command)
              end = timer()
              row = ["lean-simp", i, str(end - start)]
            except:
              row = ["lean-simp", i, "ERR"]
            assert len(row) == len(G_DATA_HEADER)
            logging.debug(row)
            writer.writerow(row)
            OUTFILE.flush(); os.fsync(OUTFILE)
            # COQ runner
            testpath = cwd / "build" / "coq" / f"n{i}.v"
            with open(testpath, "w") as f:
                f.write(count_program_coq(i))
            command = ['coqc', testpath]
            start = timer()
            try:
              subprocess.check_call(command)
              end = timer()
              row = ["coq", i, str(end - start)]
            except:
              row = ["coq", i, "ERR"]
            assert len(row) == len(G_DATA_HEADER)
            logging.debug(row)
            writer.writerow(row)
            OUTFILE.flush(); os.fsync(OUTFILE)

def plot(logging, cwd, rootdir):
    os.chdir(rootdir / "Evaluation" / "scaling")
    logging.debug(f"calling R for plotting")
    try:
      subprocess.check_call(["Rscript", "plotscaling.R", G_STATS_FILENAME()])
      return
    except:
       logging.debug("fallback to matplotlib...")
    logging.debug(f"opening {cwd / G_STATS_FILENAME()}")
    df = pd.read_csv(cwd / G_STATS_FILENAME())
    # df["time"].plot(kind="bar", legend=True)
    # plt.show()
    # print(df)

    matplotlib.rcParams['pdf.fonttype'] = 42
    matplotlib.rcParams['ps.fonttype'] = 42

    matplotlib.rcParams['figure.figsize'] = 5, 2
    dfpivot = df.pivot(index="problemsize", columns="tool", values="time")
    light_gray = "#cacaca"
    dark_gray = "#827b7b"
    light_blue = "#a6cee3"
    dark_blue = "#1f78b4"
    light_green = "#b2df8a"
    dark_green = "#33a02c"
    light_red = "#fb9a99"
    dark_red = "#e31a1c"
    colors = [dark_green, light_blue, dark_red]
    ax = dfpivot.plot(kind="line", color=colors); 

    # men_means = [1.5, 1.2, 1.3, 1.1, 1.0]
    # women_means = [1.8, 1.5, 1.1, 1.3, 0.9]


    # # Color palette

    xlabels = list(df["problemsize"].unique())
    x = np.arange(len(xlabels))  # the label locations
    # width = 0.35  # the width of the bars

    # fig, ax = plt.subplots()
    # rects1 = ax.bar(x - width/2, men_means, width, label='Men', color = light_blue)
    # rects2 = ax.bar(x + width/2, women_means, width, label='Women', color = dark_blue)

    # # Y-Axis Label
    # #
    # # Use a horizontal label for improved readability.
    ax.set_ylabel('Total Time(s)', rotation='horizontal', position = (1, 1.05),
        horizontalalignment='left', verticalalignment='bottom')

    # # Add some text for labels, title and custom x-axis tick labels, etc.
    ax.set_xticks(x)
    ax.set_xticklabels(xlabels)
    ax.legend(ncol=100, frameon=False, loc='lower right', bbox_to_anchor=(0, 1, 1, 0))

    # # Hide the right and top spines
    # #
    # # This reduces the number of lines in the plot. Lines typically catch
    # # a readers attention and distract the reader from the actual content.
    # # By removing unnecessary spines, we help the reader to focus on
    # # the figures in the graph.
    ax.spines['right'].set_visible(False)
    ax.spines['top'].set_visible(False)

    fig = ax.figure
    fig.tight_layout()

    filename = os.path.basename(__file__).replace(".py", ".pdf")
    fig.savefig(cwd / filename)

    filename = os.path.basename(__file__).replace(".py", ".png")
    fig.savefig(cwd / filename)

# Split into two parts, one that runs the tests and one that plots.
if __name__ == "__main__":
    logging.basicConfig(level=logging.DEBUG)
    cwd = Path.cwd()
    logging.debug(f"cwd: {cwd}")
    rootdir = find_repo(cwd)
    logging.debug(f"rootdir: {rootdir}")
    assert rootdir, "Expected to find .git repo from path {path}"
    os.chdir(rootdir)

    parser = argparse.ArgumentParser(description='Evaluation')
    parser.add_argument('-run', help='run the evaluation benchmark, save benchmark to file', action='store_true')
    parser.add_argument('-plot', help='plot the saved benchmarks', action='store_true')

    args = parser.parse_args()
    if not args.run and not args.plot: parser.print_help()
    if args.run:
        run(logging=logging, cwd=cwd,rootdir=rootdir)

    if args.plot:
        plot(logging=logging,cwd=cwd,rootdir=rootdir)
