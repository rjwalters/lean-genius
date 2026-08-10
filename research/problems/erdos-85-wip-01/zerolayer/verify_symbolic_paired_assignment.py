#!/usr/bin/env python3
"""Supplementally verify the paired-quotient symbolic SAT options.

The manifest-pinned base verifier remains the certificate gate for the full
H-relaxation.  This independent consumer additionally checks the normalized
phase symmetry and the exact (0 1)(2 3) omitted-type quotient directly from
the retained edge/phase assignment, ignoring every CNF auxiliary.
"""

from itertools import combinations
import sys

from verify_hlift_assignment import parse_kissat_assignment
from verify_symbolic_hlift_assignment import (
    EDGE_COUNT, N, ORPHANS, extract_witness, phase_variable_map,
)


def verify_phase_normal_form(witness):
    def links(omit):
        return [e for e in range(4) if e != omit]
    for omit in range(4):
        second = links(omit)[1]
        values = [witness[omit, copy][second] for copy in range(4)]
        if values != sorted(values):
            raise ValueError(f"copy-order failure at omitted type {omit}")
    for orphan, component in [((0, 0), 2), ((0, 0), 3), ((1, 0), 2)]:
        if witness[orphan][component] >= 3:
            raise ValueError(f"rotation-anchor failure at {orphan},{component}")


def verify_paired_quotient(edge_values):
    all_pairs = [frozenset(pair) for pair in combinations(range(N), 2)]
    neighbors = [set() for _ in range(N)]
    for pair, present in zip(all_pairs, edge_values):
        if present:
            u, v = sorted(pair)
            neighbors[u].add(v)
            neighbors[v].add(u)
    paired = {0: 1, 1: 0, 2: 3, 3: 2}
    for vertex in range(N):
        source = ORPHANS[vertex // 12][0]
        counts = [0] * 4
        for other in neighbors[vertex]:
            counts[ORPHANS[other // 12][0]] += 1
        expected = [1 if target == paired[source] else 4
                    for target in range(4)]
        if counts != expected:
            raise ValueError(f"paired quotient failure at {vertex}: "
                             f"{counts} != {expected}")
    return {"pairing": "(0 1)(2 3)", "class_size": 48,
            "quotient": "4J-3P"}


def self_test():
    # A synthetic quotient-only graph: four 48-cycles with offsets ±1,±2;
    # perfect matchings on paired classes; four-shift bipartite graphs on the
    # other class pairs.  It need not satisfy the full H common-neighbor law.
    edges = set()
    for omit in range(4):
        base = 48 * omit
        for x in range(48):
            for delta in (1, 2):
                edges.add(frozenset((base + x, base + (x + delta) % 48)))
    paired_pairs = {(0, 1), (2, 3)}
    for left, right in combinations(range(4), 2):
        shifts = (0,) if (left, right) in paired_pairs else range(4)
        for x in range(48):
            for shift in shifts:
                edges.add(frozenset((48 * left + x,
                                     48 * right + (x + shift) % 48)))
    all_pairs = [frozenset(pair) for pair in combinations(range(N), 2)]
    values = [pair in edges for pair in all_pairs]
    assert verify_paired_quotient(values)["quotient"] == "4J-3P"
    values[0] = not values[0]
    try:
        verify_paired_quotient(values)
        raise AssertionError("tampered quotient accepted")
    except ValueError as exc:
        assert "paired quotient failure" in str(exc)
    print("PAIRED OPTION VERIFIER SELF-TEST OK")


def main():
    if len(sys.argv) == 2 and sys.argv[1] == "--self-test":
        self_test()
        return
    if len(sys.argv) != 2:
        raise SystemExit(f"usage: {sys.argv[0]} KISSAT_LOG | --self-test")
    _mapping, last_phase = phase_variable_map()
    assignment = parse_kissat_assignment(sys.argv[1], last_phase)
    witness = extract_witness(assignment)
    verify_phase_normal_form(witness)
    edge_values = []
    for variable in range(1, EDGE_COUNT + 1):
        if variable not in assignment:
            raise ValueError(f"missing edge variable {variable}")
        edge_values.append(assignment[variable])
    result = verify_paired_quotient(edge_values)
    print("VERIFIED SYMBOLIC OPTIONS", result)


if __name__ == "__main__":
    main()
