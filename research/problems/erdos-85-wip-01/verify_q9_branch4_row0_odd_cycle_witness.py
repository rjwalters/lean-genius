#!/usr/bin/env python3
"""Verify the durable branch-4 row-0 odd-cycle interval deficit."""
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
    degree = [6 if u >= N_TRIPLE - 4 else 5 for u in range(N)]

    def independent(choice) -> bool:
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

    row = 0
    assert reverse_forced[row] == set()
    residual = sorted(set(candidates[row]) & reverse_possible[row])
    residual_blocks = {v: sorted(blocks[v]) for v in residual}
    assert residual_blocks == {
        3: [3, 11, 19],
        19: [7, 9, 22],
        26: [12, 18],
        29: [11, 22],
        30: [9, 16],
        32: [8, 19],
        33: [2, 22],
        38: [3, 16],
        42: [2, 8],
        45: [7, 12],
    }

    def matching_number(rows: tuple[int, ...] | list[int]) -> int:
        for size in range(len(rows), -1, -1):
            if any(independent(choice) for choice in combinations(rows, size)):
                return size
        raise AssertionError("empty matching should always exist")

    def cover_number(rows: tuple[int, ...] | list[int]) -> int:
        points = sorted(set().union(*(blocks[v] for v in rows)))
        for size in range(len(points) + 1):
            if any(
                all(blocks[v] & set(cover) for v in rows)
                for cover in combinations(points, size)
            ):
                return size
        raise AssertionError("all points cover every residual block")

    nu = matching_number(residual)
    tau = cover_number(residual)
    assert (nu, tau) == (4, 5)

    # Exhaustively minimize the non-Koenig obstruction.  No subhypergraph on
    # fewer than five blocks has tau > nu; exactly two five-block cores do.
    first_gap_size = None
    first_gap_cores = []
    for size in range(1, len(residual) + 1):
        gaps = [
            rows for rows in combinations(residual, size)
            if cover_number(rows) > matching_number(rows)
        ]
        if gaps:
            first_gap_size = size
            first_gap_cores = gaps
            break
    expected_cores = [
        (3, 19, 29, 30, 38),
        (3, 29, 32, 33, 42),
    ]
    assert first_gap_size == 5
    assert first_gap_cores == expected_cores
    assert all(
        (matching_number(core), cover_number(core)) == (2, 3)
        for core in expected_cores
    )

    # Consecutive intersections display the two Berge C5 cycles explicitly.
    cycles = [
        ((3, 29, 19, 30, 38), (11, 22, 9, 16, 3)),
        ((3, 29, 33, 42, 32), (11, 22, 2, 8, 19)),
    ]
    for rows, labels in cycles:
        for i, label in enumerate(labels):
            assert blocks[rows[i]] & blocks[rows[(i + 1) % 5]] == {label}

    print("outer_constraints=SAT branch=4 row=0")
    print(f"residual_blocks={residual_blocks}")
    print("matching_number=4 point_cover_number=5")
    print(f"minimum_non_koenig_cores={first_gap_cores}")
    print("berge_c5_labels=[[11,22,9,16,3],[11,22,2,8,19]]")
    print("odd_cycle_interval_deficit=VERIFIED")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
