#!/usr/bin/env python3
"""Exhaustively test the local encoder's sequential exact counter."""

from itertools import product
from pathlib import Path


def build(n, k):
    source = Path(__file__).with_name(
        "model4444_symbolic_sparse_defect.py").read_text()
    start = source.index("def card_eq_sequential")
    end = source.index("\n\n# Gauge-fixed", start)
    scope = {"nv": n, "clauses": []}
    exec("def newvar():\n global nv\n nv += 1\n return nv\n\n" +
         source[start:end], scope)
    scope["card_eq_sequential"](list(range(1, n + 1)), k)
    return scope["clauses"], scope["nv"]


def satisfied(clauses, assignment):
    return all(any((lit > 0) == assignment[abs(lit)] for lit in clause)
               for clause in clauses)


for n in range(1, 6):
    for k in range(1, n + 1):
        clauses, variables = build(n, k)
        for inputs in product((False, True), repeat=n):
            extendable = False
            for aux in product((False, True), repeat=variables - n):
                assignment = {i + 1: value for i, value in enumerate(inputs)}
                assignment.update({n + i + 1: value for i, value in enumerate(aux)})
                if satisfied(clauses, assignment):
                    extendable = True
                    break
            assert extendable == (sum(inputs) == k), (n, k, inputs)

print("SPARSE DEFECT SEQUENTIAL CARDINALITY ALL OK")
