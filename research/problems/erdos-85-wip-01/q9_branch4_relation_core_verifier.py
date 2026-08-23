#!/usr/bin/env python3
"""Exact four-row residual-relation obstruction in the durable branch-4 model.

The outer payload is independently pinned and checked by
``verify_q9_branch4_row40_interval_witness.py``.  Here we enumerate every
mutually trace-eligible, block-disjoint demanded neighborhood at rows
6, 15, 23, and 28.  Their four B0 blocks share U1 point 14, so residual
Gram orthogonality makes the four chosen neighborhoods pairwise disjoint.
Symmetry additionally requires each internal core edge to be chosen at both
ends.  Exhaustion leaves four possible internal-edge patterns, and none
admits pairwise-disjoint neighborhood choices.
"""

from __future__ import annotations

import json
from collections import Counter
from itertools import combinations, product
from pathlib import Path


HERE = Path(__file__).resolve().parent
PAYLOAD = HERE / "q9_branch4_row40_interval_witness.json"
ROWS = (6, 15, 23, 28)
DEMAND = {6: 5, 15: 5, 23: 6, 28: 6}
CORE_EDGES = ((6, 15), (6, 28), (15, 28), (23, 28))


def main() -> int:
    witness = json.loads(PAYLOAD.read_text())
    blocks = [set(block) for block in witness["blocks"]]
    k_neighbors = [set() for _ in range(24)]
    for a, b in witness["k_edges"]:
        k_neighbors[a].add(b)
        k_neighbors[b].add(a)
    cores = [set().union(*(k_neighbors[b] for b in block)) for block in blocks]

    def eligible(u: int, v: int) -> bool:
        return u != v and not blocks[v] & cores[u]

    assert set.intersection(*(blocks[u] for u in ROWS)) == {14}
    families: dict[int, list[frozenset[int]]] = {}
    candidates: dict[int, list[int]] = {}
    for u in ROWS:
        candidates[u] = [
            v for v in range(47) if eligible(u, v) and eligible(v, u)
        ]
        families[u] = [
            frozenset(choice)
            for choice in combinations(candidates[u], DEMAND[u])
            if all(not blocks[v] & blocks[w]
                   for v, w in combinations(choice, 2))
        ]

    assert [len(candidates[u]) for u in ROWS] == [13, 13, 12, 21]
    assert [len(families[u]) for u in ROWS] == [21, 36, 7, 308]
    expected_patterns = {
        6: {(): 14, (28,): 7},
        15: {(): 10, (6,): 6, (28,): 20},
        23: {(): 3, (28,): 4},
        28: {(): 227, (6,): 8, (15,): 39, (23,): 34},
    }
    actual_patterns = {
        u: Counter(tuple(v for v in ROWS if v in choice)
                   for choice in families[u])
        for u in ROWS
    }
    assert actual_patterns == expected_patterns

    def admits_disjoint_choices(
            restricted: dict[int, list[frozenset[int]]]) -> bool:
        def search(index: int, used: frozenset[int]) -> bool:
            if index == len(ROWS):
                return True
            u = ROWS[index]
            return any(not choice & used and search(index + 1, used | choice)
                       for choice in restricted[u])
        return search(0, frozenset())

    surviving = []
    for bits in product((False, True), repeat=len(CORE_EDGES)):
        internal = dict(zip(CORE_EDGES, bits))
        restricted = {
            u: [
                choice for choice in families[u]
                if all((v in choice) == internal.get(tuple(sorted((u, v))), False)
                       for v in ROWS if v != u)
            ]
            for u in ROWS
        }
        if any(not restricted[u] for u in ROWS):
            continue
        edge_pattern = tuple(edge for edge in CORE_EDGES if internal[edge])
        sizes = tuple(len(restricted[u]) for u in ROWS)
        surviving.append((edge_pattern, sizes))
        assert not admits_disjoint_choices(restricted)

    expected_surviving = [
        ((), (14, 10, 3, 227)),
        (((23, 28),), (14, 10, 4, 34)),
        (((15, 28),), (14, 20, 3, 39)),
        (((6, 28),), (7, 10, 3, 8)),
    ]
    assert surviving == expected_surviving
    print("common_core_point=14")
    print("candidate_counts=13,13,12,21")
    print("packing_counts=21,36,7,308")
    print("symmetric_internal_patterns=4")
    print("pairwise_disjoint_pattern_extensions=0")
    print("four_row_relation_core=VERIFIED")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
