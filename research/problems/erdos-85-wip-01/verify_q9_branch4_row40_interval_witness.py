#!/usr/bin/env python3
"""Verify the durable branch-4 row-40 contracted interval deficit."""
from __future__ import annotations

import json
from itertools import combinations
from pathlib import Path

from z3 import Not, sat

from q9_b0_residual_defect_sat import N, N_TRIPLE, N_U1, build, edge_key
from q9_gram_obstruction_negation_sat import OUTER_ONLY_RELAX


def main() -> int:
    witness = json.loads(
        Path(__file__).with_name(
            "q9_branch4_row40_interval_witness.json"
        ).read_text()
    )
    blocks = [set(row) for row in witness["blocks"]]
    k_edges = {edge_key(*edge) for edge in witness["k_edges"]}

    outer, symbolic = build(4, 60_000, True, relax=OUTER_ONLY_RELAX)
    for u in range(N):
        for b in range(N_U1):
            variable = symbolic["incidence"][u, b]
            outer.add(variable if b in blocks[u] else Not(variable))
    for edge, variable in symbolic["k"].items():
        outer.add(variable if edge in k_edges else Not(variable))
    assert outer.check() == sat

    k_neighbors = [set() for _ in range(N_U1)]
    for a, b in k_edges:
        k_neighbors[a].add(b)
        k_neighbors[b].add(a)
    cores = [set().union(*(k_neighbors[b] for b in block)) for block in blocks]
    candidates = [
        [v for v in range(N) if v != u and not blocks[v] & cores[u]]
        for u in range(N)
    ]
    holes_begin = N_TRIPLE - 4
    degree = [6 if u >= holes_begin else 5 for u in range(N)]

    def independent(choice: tuple[int, ...] | list[int]) -> bool:
        return all(
            not blocks[v] & blocks[w] for v, w in combinations(choice, 2)
        )

    packings = {
        u: [
            frozenset(choice)
            for choice in combinations(candidates[u], degree[u])
            if independent(choice)
        ]
        for u in range(N)
    }
    assert all(packings.values())
    reverse_possible = {
        u: {w for w in range(N) if any(u in X for X in packings[w])}
        for u in range(N)
    }
    reverse_forced = {
        u: {w for w in range(N) if all(u in X for X in packings[w])}
        for u in range(N)
    }

    row = 40
    forced = reverse_forced[row]
    impossible_candidates = set(candidates[row]) - reverse_possible[row]
    compatible = [
        X for X in packings[row]
        if forced <= X <= reverse_possible[row]
    ]
    assert forced == {1, 9, 24}
    assert impossible_candidates == set()
    assert len(packings[row]) == 192
    assert compatible == []

    # Exact capacity: a size-five prepacking containing F exists, while no
    # size-six one exists.  Any larger prepacking would contain such a
    # size-six subset (F plus three of its other members), so the capacity is 5.
    allowed = sorted(set(candidates[row]) & reverse_possible[row])
    size_five = [
        frozenset(choice)
        for choice in combinations(allowed, 5)
        if forced <= set(choice) and independent(choice)
    ]
    size_six = [
        frozenset(choice)
        for choice in combinations(allowed, 6)
        if forced <= set(choice) and independent(choice)
    ]
    assert size_five
    assert not size_six

    # Transparent contracted residual certificate.  After fixing F, only
    # these five block-vertices remain compatible with every forced block.
    # Their compatibility graph has three edges and no triangle, so at most
    # two residual vertices can be added to the three forced ones.
    residual = [
        v for v in allowed
        if v not in forced and all(not blocks[v] & blocks[f] for f in forced)
    ]
    residual_blocks = {v: sorted(blocks[v]) for v in residual}
    residual_pairs = [
        pair for pair in combinations(residual, 2)
        if not blocks[pair[0]] & blocks[pair[1]]
    ]
    residual_triples = [
        triple for triple in combinations(residual, 3)
        if independent(triple)
    ]
    assert residual_blocks == {
        17: [6, 8, 21],
        23: [5, 14, 19],
        32: [8, 19],
        35: [6, 19],
        42: [2, 8],
    }
    assert residual_pairs == [(17, 23), (23, 42), (35, 42)]
    assert residual_triples == []

    print("outer_constraints=SAT branch=4 row=40")
    print(
        "forced=[1,9,24] impossible_candidates=[] "
        "demand=6 interval_capacity=5"
    )
    print(
        f"row_packings={len(packings[row])} "
        f"capacity_five_witnesses="
        f"{[sorted(X) for X in size_five]}"
    )
    print(
        f"residual_blocks={residual_blocks} "
        f"compatible_pairs={residual_pairs} compatible_triples=[]"
    )
    print("contracted_interval_deficit=VERIFIED")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
