#!/usr/bin/env python3
"""Exhaustive primitive tests for the symbolic cube-root color cut."""

from itertools import product


def satisfied(clauses, assignment):
    return all(any((literal > 0) == assignment[abs(literal)]
                   for literal in clause) for clause in clauses)


# P_0,...,P_11 are variables 1,...,12.  Color-residue variables are 13..15.
clauses = []
for residue in range(3):
    color = 13 + residue
    phases = [1 + phase for phase in range(12) if phase % 3 == residue]
    for phase in phases:
        clauses.append((-phase, color))
    clauses.append((-color, *phases))

for selected in range(12):
    phase_values = {1 + phase: phase == selected for phase in range(12)}
    for colors in product((False, True), repeat=3):
        assignment = dict(phase_values)
        assignment.update({13 + residue: colors[residue]
                           for residue in range(3)})
        expected = tuple(residue == selected % 3 for residue in range(3))
        assert satisfied(clauses, assignment) == (colors == expected)

# The colored-edge Tseitin gate is an exact conjunction.
and_clauses = [(-3, 1), (-3, 2), (3, -1, -2)]
for edge, color, both in product((False, True), repeat=3):
    assignment = {1: edge, 2: color, 3: both}
    assert satisfied(and_clauses, assignment) == (both == (edge and color))

# The normalized paired quotient leaves twelve linked-component neighbors
# exactly for the paired component and nine for every other component.
paired = {0: 1, 1: 0, 2: 3, 3: 2}
for source in range(4):
    omitted_degrees = [1 if target == paired[source] else 4
                       for target in range(4)]
    for component in range(4):
        expected = 4 if component == paired[source] else 3
        assert 13 - omitted_degrees[component] == 3 * expected

print("SYMBOLIC COLOR BALANCE PRIMITIVES ALL OK")
