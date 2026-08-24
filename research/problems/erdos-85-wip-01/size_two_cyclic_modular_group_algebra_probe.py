#!/usr/bin/env python3
"""Calibrate the F2[Z/2^k] augmentation filtration on cyclic routing models.

For a subset R of relative base displacements, encode its row polynomial as

    f_R(z) = sum_{r in R} z^r  in F2[z]/(z^q-1).

When q is a power of two this ring is F2[eps]/(eps^q), eps=z+1.  The script
extracts exact SAT models from ``size_two_cyclic_exact_graph_probe`` and
reports eps-adic valuations of every target-difference part of every routing
row.  In particular, a two-route collision at separation d has valuation
2^v2(d); this tests whether reciprocity changes, raises, or merely preserves
the proposed 2-adic collision level.

With ``--pairing-profile``, it also folds every partial-permutation block
modulo q/2, cancels double lifts over F2, and classifies the canonical pairing
of its four odd boundary vertices.  Lift-voltage identities from
``SIZE_TWO_CYCLIC_HALF_QUOTIENT_PAIRING_PROBE.md`` are checked exactly.

The default q=4 run uses the full same-difference cap.  At q=8 one can pass
``--c4-difference`` twice to inspect the known satisfiable two-fiber
relaxations; adding 0,2,4 is UNSAT for a=1.
"""

from __future__ import annotations

import argparse
from collections import Counter
from itertools import combinations
from math import comb

import z3

from size_two_cyclic_exact_graph_probe import build


def augmentation_valuation(exponents: list[int], q: int) -> int:
    """Return the (z+1)-adic valuation, with q for the zero polynomial."""
    for degree in range(q):
        coefficient = sum(comb(r, degree) for r in exponents) % 2
        if coefficient:
            return degree
    return q


def v2(n: int) -> int:
    assert n > 0
    value = 0
    while n % 2 == 0:
        value += 1
        n //= 2
    return value


def half_quotient_signature(
    routes: list[tuple[int, int]], source_t: int, q: int
) -> tuple[str, tuple[tuple[str, int], ...], tuple[int, int]]:
    """Return the canonical boundary pairing and reverse-voltage signature.

    A route is ``(relative target row, relative target column)``.  Folding
    modulo ``q/2`` and cancelling cells with even multiplicity gives a
    bipartite graph of maximum degree two with four prescribed odd vertices.
    The two path components pair those vertices.  Each surviving edge is
    labelled by the high-bit xor of its reversed relative coordinates
    ``(-r, source_t-r)``.
    """
    m = q // 2
    cells: dict[tuple[int, int], list[tuple[int, int]]] = {}
    for row, column in routes:
        cells.setdefault((row % m, column % m), []).append((row, column))
    surviving = {cell: lifts for cell, lifts in cells.items() if len(lifts) % 2}
    assert all(len(lifts) == 1 for lifts in surviving.values())

    adjacency: dict[tuple[str, int], list[tuple[tuple[str, int], tuple[int, int]]]] = {}
    for cell in surviving:
        row_node = ("R", cell[0])
        col_node = ("C", cell[1])
        adjacency.setdefault(row_node, []).append((col_node, cell))
        adjacency.setdefault(col_node, []).append((row_node, cell))
    assert all(len(edges) <= 2 for edges in adjacency.values())

    boundary_names = {
        ("R", source_t % m): "R0",
        ("R", (source_t + 1) % m): "R1",
        ("C", 0): "C0",
        ("C", (-1) % m): "C1",
    }
    odd = {node for node, edges in adjacency.items() if len(edges) % 2}
    assert odd == set(boundary_names), (source_t, odd, set(boundary_names))

    def reverse_voltage(cell: tuple[int, int]) -> int:
        row, _column = surviving[cell][0]
        return (((-row) % q) // m) ^ (((source_t - row) % q) // m)

    visited_edges: set[tuple[int, int]] = set()
    paths: list[tuple[str, int]] = []
    path_lengths: list[int] = []
    for start in sorted(odd):
        incident = [cell for _neighbor, cell in adjacency[start]
                    if cell not in visited_edges]
        if not incident:
            continue
        node = start
        voltage = 0
        length = 0
        while True:
            choices = [(neighbor, cell) for neighbor, cell in adjacency[node]
                       if cell not in visited_edges]
            if not choices:
                break
            assert len(choices) == 1
            neighbor, cell = choices[0]
            visited_edges.add(cell)
            voltage ^= reverse_voltage(cell)
            length += 1
            node = neighbor
        assert node in odd and node != start
        endpoint_pair = "-".join(sorted((boundary_names[start], boundary_names[node])))
        paths.append((endpoint_pair, voltage))
        path_lengths.append(length)

    # Every remaining component is a cycle and has zero reverse voltage.
    for first_cell in surviving:
        if first_cell in visited_edges:
            continue
        node = ("R", first_cell[0])
        cycle_voltage = 0
        while True:
            choices = [(neighbor, cell) for neighbor, cell in adjacency[node]
                       if cell not in visited_edges]
            if not choices:
                break
            neighbor, cell = choices[0]
            visited_edges.add(cell)
            cycle_voltage ^= reverse_voltage(cell)
            node = neighbor
        assert cycle_voltage == 0
    assert len(visited_edges) == len(surviving)
    assert len(paths) == 2

    pairs = sorted(pair for pair, _voltage in paths)
    if all(pair[0] == pair[3] for pair in pairs):
        pairing = "RR|CC"
    else:
        pairing = "|".join(pairs)
    assert sum(voltage for _pair, voltage in paths) % 2 == int(source_t % m != 0)
    return pairing, tuple(sorted(paths)), tuple(sorted(path_lengths))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("q", type=int)
    parser.add_argument("--a", type=int, required=True)
    parser.add_argument("--timeout-ms", type=int, default=300_000)
    parser.add_argument("--random-seed", type=int, default=0)
    parser.add_argument("--c4-difference", type=int, action="append")
    parser.add_argument("--pairing-profile", action="store_true")
    parser.add_argument(
        "--profile-difference", type=int, action="append",
        help="differences whose pairing types are grouped jointly by base",
    )
    args = parser.parse_args()

    q = args.q
    assert q >= 2 and q & (q - 1) == 0, "q must be a power of two"
    if args.pairing_profile:
        assert q >= 4, "the four-boundary pairing needs q/2 > 1"
    selected = None if args.c4_difference is None else {
        t % q for t in args.c4_difference
    }
    solver, vertices, edge = build(
        q,
        args.a,
        c4_pair_mode="same-difference",
        c4_differences=selected,
    )
    solver.set(timeout=args.timeout_ms, random_seed=args.random_seed)
    result = solver.check()
    print(f"q={q} a={args.a % q} selected={selected}: {result}")
    if result != z3.sat:
        return

    model = solver.model()
    index = {vertex: i for i, vertex in enumerate(vertices)}

    def adjacent(u: tuple[int, int], v: tuple[int, int]) -> bool:
        i, j = index[u], index[v]
        if i == j:
            return False
        return z3.is_true(model.eval(edge[min(i, j), max(i, j)]))

    allowed = sorted({(y - x) % q for x, y in vertices})
    part_valuations: Counter[tuple[int, int]] = Counter()
    collision_pair_levels: Counter[tuple[int, int]] = Counter()
    half_quotient_signatures: Counter[
        tuple[int, str, tuple[tuple[str, int], ...]]
    ] = Counter()
    collision_count = 0
    pairing_profiles: Counter[tuple[int, str]] = Counter()
    pairing_path_lengths: Counter[tuple[int, str, tuple[int, int]]] = Counter()
    pairing_by_block: dict[tuple[int, int], str] = {}

    for x, y in vertices:
        source_t = (y - x) % q
        aggregate: list[int] = []
        routes: list[tuple[int, int]] = []
        for target_s in allowed:
            displacements = []
            for target_x in range(q):
                target = (target_x, (target_x + target_s) % q)
                if target in index and adjacent((x, y), target):
                    displacements.append((target_x - x) % q)
            if not displacements:
                continue
            aggregate.extend(displacements)
            routes.extend((r, (r + target_s) % q) for r in displacements)
            valuation = augmentation_valuation(displacements, q)
            part_valuations[(len(displacements), valuation)] += 1
            for r, s in combinations(displacements, 2):
                collision_count += 1
                separation = (s - r) % q
                level = augmentation_valuation([r, s], q)
                predicted = 1 << v2(separation)
                assert level == predicted, (r, s, level, predicted)
                collision_pair_levels[(v2(separation), level)] += 1

        expected = [r for r in range(q) if r not in {source_t, (source_t + 1) % q}]
        assert sorted(aggregate) == expected
        assert augmentation_valuation(aggregate, q) == 1
        if q >= 4:
            pairing, path_voltages, path_lengths = half_quotient_signature(
                routes, source_t, q
            )
            half_quotient_signatures[(source_t, pairing, path_voltages)] += 1
            if args.pairing_profile:
                pairing_profiles[(source_t, pairing)] += 1
                pairing_path_lengths[(source_t, pairing, path_lengths)] += 1
                pairing_by_block[(x, source_t)] = pairing

    print(f"vertices={len(vertices)} allowed_differences={allowed}")
    print("target-part (cardinality, eps-valuation) distribution:")
    for key, count in sorted(part_valuations.items()):
        print(f"  {key}: {count}")
    print(f"collision_pairs={collision_count}")
    print("collision (v2(separation), eps-valuation) distribution:")
    for key, count in sorted(collision_pair_levels.items()):
        print(f"  {key}: {count}")
    if q >= 4:
        print("half-quotient (source_t, pairing, path reverse voltages) distribution:")
        for key, count in sorted(half_quotient_signatures.items()):
            print(f"  {key}: {count}")
    if args.pairing_profile:
        print("folded (difference, pairing) distribution:")
        for key, count in sorted(pairing_profiles.items()):
            print(f"  {key}: {count}")
        print("folded (difference, pairing, boundary path lengths) distribution:")
        for key, count in sorted(pairing_path_lengths.items()):
            print(f"  {key}: {count}")
        profiled = (allowed if args.profile_difference is None else
            [t % q for t in args.profile_difference])
        assert all(t in allowed for t in profiled)
        joint: Counter[tuple[str, ...]] = Counter()
        for x in range(q):
            joint[tuple(pairing_by_block[x, t] for t in profiled)] += 1
        print(f"joint pairing profiles for differences {profiled}:")
        for profile, count in sorted(joint.items()):
            print(f"  {profile}: {count}")


if __name__ == "__main__":
    main()
