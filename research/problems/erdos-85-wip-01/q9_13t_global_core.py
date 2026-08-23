#!/usr/bin/env python3
"""Extract a smallest row core from the durable counterexample to (13t).

The global selection problem is a finite-domain binary CSP: row ``u``
chooses one demanded packing, and rows ``u,v`` must agree on the bit saying
whether they select one another.  This verifier exhaustively checks every
one-, two-, then three-row induced CSP and prints the first UNSAT core.
"""
from __future__ import annotations

import json
from itertools import combinations, product
from pathlib import Path

from q9_b0_residual_defect_sat import N, N_U1, edge_key


def load_instance() -> tuple[list[set[int]], list[set[int]], list[int]]:
    witness = json.loads(
        Path(__file__).with_name("q9_13t_counterexample.json").read_text()
    )
    blocks = [set(row) for row in witness["blocks"]]
    k_edges = {edge_key(*edge) for edge in witness["k_edges"]}
    kn = [set() for _ in range(N_U1)]
    for a, b in k_edges:
        kn[a].add(b)
        kn[b].add(a)
    cores = [set().union(*(kn[b] for b in block)) for block in blocks]
    candidates = [
        {v for v in range(N) if v != u and not blocks[v] & cores[u]}
        for u in range(N)
    ]
    degree = [5 if u < 24 else 6 for u in range(N)]
    return blocks, candidates, degree


def packing_domains(
    blocks: list[set[int]], candidates: list[set[int]], degree: list[int]
) -> list[list[frozenset[int]]]:
    return [
        [
            frozenset(choice)
            for choice in combinations(candidates[u], degree[u])
            if all(not blocks[v] & blocks[w] for v, w in combinations(choice, 2))
        ]
        for u in range(N)
    ]


def compatible_assignment(
    rows: tuple[int, ...], domains: list[list[frozenset[int]]]
) -> tuple[frozenset[int], ...] | None:
    def search(chosen: tuple[frozenset[int], ...]):
        if len(chosen) == len(rows):
            return chosen
        u = rows[len(chosen)]
        for packing in domains[u]:
            if all(
                (v in packing) == (u in reverse)
                for v, reverse in zip(rows, chosen)
            ):
                found = search(chosen + (packing,))
                if found is not None:
                    return found
        return None

    return search(())


def main() -> int:
    blocks, candidates, degree = load_instance()
    domains = packing_domains(blocks, candidates, degree)
    assert all(domains)

    core = None
    for size in (1, 2, 3):
        for rows in combinations(range(N), size):
            if compatible_assignment(rows, domains) is None:
                core = rows
                break
        if core is not None:
            break
    assert core is not None
    assert len(core) == 3, core
    assert all(
        compatible_assignment(pair, domains) is not None
        for pair in combinations(core, 2)
    )

    print(f"minimum_row_unsat_core={list(core)} size={len(core)}")
    for u in core:
        others = tuple(v for v in core if v != u)
        patterns = sorted(
            {tuple(int(v in packing) for v in others) for packing in domains[u]}
        )
        print(
            f"row={u} packings={len(domains[u])} other_rows={list(others)} "
            f"membership_patterns={patterns}"
        )

    # Verify all eight symmetric edge assignments fail.  The edge order is
    # (core[0],core[1]), (core[0],core[2]), (core[1],core[2]).
    edges = tuple(combinations(core, 2))
    for bits in product((0, 1), repeat=len(edges)):
        edge_bit = {edge: bit for edge, bit in zip(edges, bits)}
        row_ok = []
        for u in core:
            row_ok.append(
                any(
                    all(
                        int(v in packing) == edge_bit[tuple(sorted((u, v)))]
                        for v in core
                        if v != u
                    )
                    for packing in domains[u]
                )
            )
        assert not all(row_ok), (bits, row_ok)

    print("all_singletons_and_pairs=SAT")
    print("all_eight_symmetric_edge_assignments=UNSAT")
    print("minimum_three_row_core=VERIFIED")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
