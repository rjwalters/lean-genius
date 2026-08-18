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


def verify_color_balance(witness, edge_values):
    """Check the cube-root color counts from retained H and phase variables."""
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
        for component in range(4):
            counts = [0, 0, 0]
            for other in neighbors[vertex]:
                orphan = ORPHANS[other // 12]
                if component not in witness[orphan]:
                    continue
                color = ((other % 12) + witness[orphan][component]) % 3
                counts[color] += 1
            expected = 4 if component == paired[source] else 3
            if counts != [expected] * 3:
                raise ValueError(
                    f"color balance failure at vertex {vertex}, component "
                    f"{component}: {counts} != {[expected] * 3}")
    return {"cube_root_color_counts": "exact", "counts": "3-or-4"}


def stage1_A_pairs(witness):
    """Reconstruct D union S directly from the retained phase witness."""
    def vid(orphan, x):
        return 12 * ORPHANS.index(orphan) + x % 12

    pairs = set()
    for orphan in ORPHANS:
        for x in range(12):
            pairs.add(frozenset((vid(orphan, x), vid(orphan, x + 1))))
    for left, right in combinations(ORPHANS, 2):
        shared = set(witness[left]) & set(witness[right])
        for component in shared:
            delta = (witness[left][component] -
                     witness[right][component]) % 12
            for x in range(12):
                pair = frozenset((vid(left, x), vid(right, x + delta)))
                if pair in pairs:
                    raise ValueError(f"duplicate Stage-1 A pair {pair}")
                pairs.add(pair)
    return pairs


def verify_global_overlap(witness, edge_values):
    all_pairs = [frozenset(pair) for pair in combinations(range(N), 2)]
    stage1 = stage1_A_pairs(witness)
    overlap = sum(present and pair in stage1
                  for pair, present in zip(all_pairs, edge_values))
    if overlap != 264:
        raise ValueError(f"global H-inter-A overlap failure: {overlap} != 264")
    return {"H_inter_A_edges": overlap}


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
    # Independently exercise the exact global-overlap consumer on the
    # validated baseline phase witness.
    from test_symbolic_hlift_service import WIT
    stage1 = stage1_A_pairs(WIT)
    selected = set(sorted(stage1, key=lambda p: tuple(sorted(p)))[:264])
    overlap_values = [pair in selected for pair in all_pairs]
    assert verify_global_overlap(WIT, overlap_values)["H_inter_A_edges"] == 264
    first = next(index for index, value in enumerate(overlap_values) if value)
    overlap_values[first] = False
    try:
        verify_global_overlap(WIT, overlap_values)
        raise AssertionError("tampered global overlap accepted")
    except ValueError as exc:
        assert "global H-inter-A overlap failure" in str(exc)
    print("PAIRED OPTION VERIFIER SELF-TEST OK")


def main():
    if len(sys.argv) == 2 and sys.argv[1] == "--self-test":
        self_test()
        return
    flags = set(sys.argv[2:])
    allowed = {"--color-balance", "--global-overlap-count"}
    if len(sys.argv) < 2 or not flags <= allowed or \
            len(flags) != len(sys.argv[2:]):
        raise SystemExit(
            f"usage: {sys.argv[0]} KISSAT_LOG [--color-balance] "
            "[--global-overlap-count] | --self-test")
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
    if "--color-balance" in flags:
        result.update(verify_color_balance(witness, edge_values))
    if "--global-overlap-count" in flags:
        result.update(verify_global_overlap(witness, edge_values))
    print("VERIFIED SYMBOLIC OPTIONS", result)


if __name__ == "__main__":
    main()
