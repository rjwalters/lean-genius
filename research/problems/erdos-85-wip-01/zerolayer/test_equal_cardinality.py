#!/usr/bin/env python3
"""Exhaustive tests for the commutation-cut cardinality equality encoder."""
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
start = src.index("def threshold_bits(lits):")
end = src.index('if "--comm-anchor" in sys.argv:', start)
body = src[start:end]

ok_all = True
for n in range(1, 4):
    ns = {}
    exec(header + body, ns)
    ns["nv"] = 2 * n
    ns["equal_cardinality"](list(range(1, n + 1)),
                            list(range(n + 1, 2 * n + 1)))
    clauses, nv = ns["clauses"], ns["nv"]
    accepted = 0
    unique = True
    for inputs in itertools.product([False, True], repeat=2 * n):
        extensions = 0
        for aux in itertools.product([False, True], repeat=nv - 2 * n):
            assign = {i + 1: inputs[i] for i in range(2 * n)}
            assign.update({2 * n + 1 + i: aux[i]
                           for i in range(nv - 2 * n)})
            if all(any(assign[abs(lit)] if lit > 0 else
                       not assign[abs(lit)] for lit in clause)
                   for clause in clauses):
                extensions += 1
        expected = sum(inputs[:n]) == sum(inputs[n:])
        accepted += extensions > 0
        unique &= extensions == (1 if expected else 0)
    expected_count = sum(__import__("math").comb(n, k) ** 2
                         for k in range(n + 1))
    ok = accepted == expected_count and unique
    ok_all &= ok
    print(f"n={n}: accepted {accepted} expect {expected_count}; "
          f"unique={unique}", "OK" if ok else "FAIL")

print("ALL OK" if ok_all else "FAILURES PRESENT")
raise SystemExit(0 if ok_all else 1)
