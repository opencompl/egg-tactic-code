import os

def count_program_lean_preamble():
    return """
    inductive B where -- bit
    | O : B
    | I : B
    open B
    """

#N : number of bits
# tactic name is (simp|rawEgg)
def count_program_lean(n: int, tactic_name: str): 
    out = ""
    out += f"def count_upward_{n}"
    out += f"\n(count: " + ("B ->" * n) + "B" + ")"
    for i in range(1, n+1):
        # [n-1, i): universally quantified
        # [i]: O
        # [i-1, 0): I
        out += f"\n(count_{i}:"
        univ_vars = [f"b{i}" for i in list(range(n, i, -1))]
        if univ_vars:
            out += "∀ (" +  " ".join(univ_vars) + ": B), "

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
    out += "\n}"
    return out

if __name__ == "__main__":
