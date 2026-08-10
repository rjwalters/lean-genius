#!/usr/bin/env python3
"""Exhaustive small tests for the symbolic conditional-common primitive."""

from itertools import product


def build(n):
    # Inputs: service=1; common-neighbor indicators 2..n+1.
    service = 1
    common = list(range(2, n + 2))
    nextvar = n + 1
    clauses = []
    for literal in common:
        clauses.append((-service, -literal))       # service -> zero
    clauses.append((service, *common))             # not service -> >= 1
    previous = None
    for literal in common[:-1]:
        nextvar += 1
        seen = nextvar
        if previous is None:
            clauses.append((-literal, seen))
        else:
            clauses.append((-previous, seen))
            clauses.append((-literal, seen))
            clauses.append((service, -literal, -previous))
        previous = seen
    if previous is not None:
        clauses.append((service, -common[-1], -previous))
    return clauses, nextvar


def satisfied(clauses, assignment):
    return all(any((literal > 0) == assignment[abs(literal)]
                   for literal in clause) for clause in clauses)


for n in range(1, 7):
    clauses, variables = build(n)
    auxiliary = list(range(n + 2, variables + 1))
    for service, bits in product((False, True), product((False, True), repeat=n)):
        extendable = False
        for aux_values in product((False, True), repeat=len(auxiliary)):
            assignment = {1: service}
            assignment.update({i + 2: bit for i, bit in enumerate(bits)})
            assignment.update(dict(zip(auxiliary, aux_values)))
            if satisfied(clauses, assignment):
                extendable = True
                break
        expected = (sum(bits) == 0) if service else (sum(bits) == 1)
        assert extendable == expected, (n, service, bits, extendable, expected)
print("ALL OK")
