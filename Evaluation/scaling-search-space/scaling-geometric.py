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


def count_program_coq_congruence(ndigits: int, radix: int):
    assert radix >= 2
    assert ndigits >= 1
    out = ""
    out += "Inductive B :=" + "| ".join(f"B{r}" for r in range(radix)) + ".\n"

    out += f"Theorem count_upward_{ndigits}_{radix}: forall"
    out += f"\n(count: " + ("B ->" * ndigits) + "B" + ")"
    for i in range(1, ndigits+1):
        for r in range(radix-1):
            # [n-1, i): universally quantified
            # [i]: O
            # [i-1, 0): I
            out += f"(count_{i}_{r}:"
            univ_vars = [f"b{i}" for i in list(range(ndigits, i, -1))]
            if univ_vars:
                out += "forall (" +  " ".join (univ_vars) + ": B), "

            # lhs
            out += "count " + " ".join(univ_vars) + f" B{r}"+ f" B{r+1}" * ((i - 1) - 0)
            out += " = "
            out += "count " + " ".join(univ_vars) + f" B{r+1}" + f" B{r}" * ((i - 1) - 0)
            out += ")\n" # rule
    out += "\n, count " + (f"B{radix-2} " * ndigits) + " = " + "count " + (f"B{radix-1} " * ndigits) + ".\n"
    out += "Proof. intros. timeout 60 (congruence 999999). Qed.\n";
    return out

def count_program_coq_autorewrite(ndigits: int, radix: int):
    assert radix >= 2
    assert ndigits >= 1
    out = ""
    out += "Inductive B :=" + "| ".join(f"B{r}" for r in range(radix)) + ".\n"
    out += f"\n Parameter count: " + ("B ->" * ndigits) + "B" + ".\n"

    for i in range(1, ndigits+1):
        for r in range(radix-1):
            # [n-1, i): universally quantified
            # [i]: O
            # [i-1, 0): I
            out += f"Axiom count_{i}_{r}:"
            univ_vars = [f"b{i}" for i in list(range(ndigits, i, -1))]
            if univ_vars:
                out += "forall (" +  " ".join (univ_vars) + ": B), "

            # lhs
            out += "count " + " ".join(univ_vars) + f" B{r}"+ f" B{r+1}" * ((i - 1) - 0)
            out += " = "
            out += "count " + " ".join(univ_vars) + f" B{r+1}" + f" B{r}" * ((i - 1) - 0)
            out += ".\n" # rule
            out += "Global Hint Rewrite " + f"count_{i}_{r}"  " : base0.\n"

    out += f"Theorem count_upward_{ndigits}: "
    out += "count " + (f"B{radix-2} " * ndigits) + " = " + "count " + (f"B{radix-1} " * ndigits) + ".\n"
    out += "Proof. intros. autorewrite with base0. reflexivity. Qed.\n";
    return out

def count_program_lean(ndigits: int, radix: int, tactic_name: str):
    """
    ndigits: number of places to keep your digits. 
    radix: base of the number system (binary, ternary, quaternary, ...)
    tactic_name: simp|eggxplosion
    """
    assert radix > 0, "expected legal radix"
    assert ndigits > 0, "expected legal number of digits"

    out = """
import EggTactic
set_option maxRecDepth 20000

inductive B where -- digit\n
"""
    for i in range(0, radix): # sorry andres, digits actually go from [0..radix-1]
        out += f"| B{i}\n" # ith digit in [1, radix]
    out += "open B\n"

    out += f"def count_upward_{ndigits}"
    out += f"\n(count: " + ("B ->" * ndigits) + "B" + ")"

    for i in range(1, ndigits+1):
        for r in range(0, radix-1):
            # ith rule says when it is legal to toggle ith bit
            # [n-1, i): universally quantified
            # [i]: O
            # [i-1, 0): I
            out += f"\n(count_{i}_{r}:"
            univ_vars = [f"b{i}" for i in list(range(ndigits, i, -1))]
            if univ_vars:
                out += "∀ (" +  " ".join (univ_vars) + ": B), "
            # smaller number. Think that O = B0, I = B1
            out += "count " + " ".join(univ_vars) + f" B{r}" + f" B{r+1}" * ((i - 1) - 0)
            out += " = "
            out += "count " + " ".join(univ_vars) + f" B{r+1}" + f" B{r}" * ((i - 1) - 0)
            out += ")" # rule
    out += "\n  : " + "count " + (f"B0 " * ndigits) + " = " + "count " + (f" B{max(0, radix-1)}" * ndigits)
    out += ":= by {"
    out += tactic_name + "["+ ", ".join([f"count_{i}_{r}" for i in range(1, ndigits+1) for r in range(0, radix-1)]) + "]";
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


def setup_run(logging, cwd, rootdir):
    """Run build system to setup benchmark runner"""
    command = ['lake', 'build']
    logging.debug("$" + " ".join(command))
    subprocess.check_call(command, cwd=rootdir)

    command = ['cargo', 'build', '--release']
    logging.debug("$" + " ".join(command))
    subprocess.check_call(command, cwd=rootdir / "json-egg")


def run(logging, cwd, rootdir):
    logging.debug("removing directory '" + str(cwd / "build") + "'")
    if (cwd / "build").exists(): shutil.rmtree(cwd / "build")
    logging.debug("making test dirs")
    os.makedirs(cwd / "build" / "lean-egg", exist_ok=True)
    os.makedirs(cwd / "build" / "lean-simp", exist_ok=True)
    os.makedirs(cwd / "build" / "coq-autorewrite", exist_ok=True)
    os.makedirs(cwd / "build" / "coq-congruence", exist_ok=True)
    errored_out = { 'lean-egg' : False, 'lean-simp' : False,
                    'coq-autorewrite' : False, 'coq-congruence' : False}

    setup_run(logging, cwd, rootdir)

    N = 60
    NDIGITS=3

    with open(cwd / G_STATS_FILENAME(), "w") as OUTFILE:
        writer = csv.writer(OUTFILE)
        writer.writerow(G_DATA_HEADER)
        for i in range(2, N+1): # Radix begins at 2 (binary)
            logging.debug(f"Generating ({i}/{N})")
            if errored_out['lean-egg'] :
              logging.debug(f"Skipping lean-egg")
            else:
              # LEAN egg runner
              testpath = cwd / "build" / "lean-egg" / f"n{i}.lean"
              with open(testpath, "w") as f:
                  f.write(count_program_lean(ndigits=NDIGITS, radix=i, tactic_name="eggxplosion"))
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
                errored_out['lean-egg'] = True
              assert len(row) == len(G_DATA_HEADER)
              logging.debug(row)
              writer.writerow(row)
              OUTFILE.flush(); os.fsync(OUTFILE)
            # LEAN simp runner
            if errored_out['lean-simp'] :
              logging.debug("Skipping lean-simp")
            else:
              testpath = cwd / "build" / "lean-simp" / f"n{i}.lean"
              with open(testpath, "w") as f:
                  f.write(count_program_lean(ndigits=NDIGITS, radix=i, tactic_name="simp"))
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
                errored_out['lean-simp'] = True
              assert len(row) == len(G_DATA_HEADER)
              logging.debug(row)
              writer.writerow(row)
              OUTFILE.flush(); os.fsync(OUTFILE)
            # COQ congruence runner
            if errored_out['coq-congruence']:
              logging.debug('Skipping coq-congruence')
            else:
              testpath = cwd / "build" / "coq-congruence" / f"n{i}.v"
              with open(testpath, "w") as f:
                  f.write(count_program_coq_congruence(ndigits=NDIGITS, radix=i))
              command = ['coqc', testpath]
              start = timer()
              try:
                subprocess.check_call(command)
                end = timer()
                row = ["coq-congruence", i, str(end - start)]
              except:
                row = ["coq-congruence", i, "ERR"]
                errored_out['coq-congruence'] = True
              assert len(row) == len(G_DATA_HEADER)
              logging.debug(row)
              writer.writerow(row)
              OUTFILE.flush(); os.fsync(OUTFILE)
            # COQ autorewrite runner
            if errored_out['coq-autorewrite']:
              logging.debug("Skpping coq-autorewrite")
            else:
              testpath = cwd / "build" / "coq-autorewrite" / f"n{i}.v"
              with open(testpath, "w") as f:
                  f.write(count_program_coq_autorewrite(ndigits=NDIGITS, radix=i))
              command = ['coqc', testpath]
              start = timer()
              try:
                subprocess.check_call(command)
                end = timer()
                row = ["coq-autorewrite", i, str(end - start)]
              except:
                row = ["coq-autorewrite", i, "ERR"]
                errored_out['coq-autorewrite'] = True
              assert len(row) == len(G_DATA_HEADER)
              logging.debug(row)
              writer.writerow(row)
              OUTFILE.flush(); os.fsync(OUTFILE)


def plot(logging, cwd, rootdir):
    os.chdir(rootdir / "Evaluation" / "scaling-search-space")
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

    print("NOTE: we have a timeout of 60 seconds for congruence")
