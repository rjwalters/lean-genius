#!/usr/bin/env python3
"""Exhaustive tests for model4444_hlift.xor_odd.

For input lengths 1 through 7, checks that exactly the odd-parity input
assignments extend to the generated clauses and that each such assignment
has exactly one auxiliary extension.  This verifies both soundness and the
equivalence (rather than implication-only) property used for propagation.
"""
import itertools
import os

SRC = os.path.join(os.path.dirname(__file__), "model4444_hlift.py")
with open(SRC, encoding="utf-8") as source:
    src = source.read()

header = """
nv = 0
clauses = []
def newvar():
    global nv
    nv += 1
    return nv
"""
start = src.index("def xor_odd(lits):")
end = src.index("for v in range(N):", start)
body = src[start:end]

ok_all = True
for n in range(1, 8):
    ns = {}
    exec(header + body, ns)
    ns["nv"] = n
    ns["xor_odd"](list(range(1, n + 1)))
    clauses, nv = ns["clauses"], ns["nv"]
    accepted = 0
    unique = True
    for bits in itertools.product([False, True], repeat=n):
        extensions = 0
        for aux in itertools.product([False, True], repeat=nv - n):
            assign = {i + 1: bits[i] for i in range(n)}
            assign.update({n + 1 + i: aux[i] for i in range(nv - n)})
            if all(any(assign[abs(lit)] if lit > 0 else
                       not assign[abs(lit)] for lit in clause)
                   for clause in clauses):
                extensions += 1
        expected = sum(bits) % 2 == 1
        accepted += extensions > 0
        unique &= extensions == (1 if expected else 0)
    expected_count = 2 ** (n - 1)
    ok = accepted == expected_count and unique
    ok_all &= ok
    print(f"n={n}: accepted {accepted} expect {expected_count}; "
          f"unique={unique}", "OK" if ok else "FAIL")

print("ALL OK" if ok_all else "FAILURES PRESENT")
raise SystemExit(0 if ok_all else 1)
