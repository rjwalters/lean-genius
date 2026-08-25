#!/usr/bin/env python3
"""Verify a same-source B.3 exchange countermodel in the outer Q/K layer."""

from itertools import combinations

from z3 import sat

from q9_b0_residual_defect_sat import build
from q9_symmetric_point_mass_obstruction import (
    N,
    OUTER_ONLY_RELAX,
    contracted_residual_rows,
    fixed_system,
    forced_local_packing_neighbors,
    local_packing_family,
)


BLOCKS = [
    [0, 8, 16], [1, 9, 17], [2, 10, 18], [3, 11, 19],
    [4, 12, 20], [5, 13, 21], [6, 14, 22], [7, 15, 23],
    [3, 12, 22], [2, 9, 19], [5, 8, 20], [1, 10, 23],
    [0, 13, 17], [4, 11, 21], [7, 14, 16], [6, 15, 18],
    [5, 15, 19], [2, 8, 22], [3, 9, 20], [7, 13, 18],
    [4, 10, 17], [6, 12, 16], [1, 14, 21], [0, 11, 23],
    [6, 10, 19], [5, 11, 22], [10, 20], [13, 22], [9, 23],
    [15, 16], [12, 21], [8, 18], [14, 17], [1, 20], [0, 21],
    [5, 23], [4, 18], [7, 19], [3, 16], [2, 17], [2, 13],
    [7, 12], [6, 11], [0, 14], [4, 9], [1, 15], [3, 8],
]

K_EDGES = [
    [0, 1], [0, 11], [0, 18], [1, 9], [1, 22], [2, 3],
    [2, 15], [2, 17], [3, 12], [3, 23], [4, 5], [4, 10],
    [4, 16], [5, 14], [5, 19], [6, 7], [6, 8], [6, 21],
    [7, 13], [7, 20], [8, 9], [8, 21], [9, 19], [10, 13],
    [10, 23], [11, 15], [11, 20], [12, 14], [12, 18],
    [13, 22], [14, 17], [15, 16], [16, 22], [17, 20],
    [18, 19], [21, 23],
]

SOURCE = 26
FIRST = 8
SECOND = 16


def main():
    payload = {"branch": 3, "blocks": BLOCKS, "k_edges": K_EDGES}
    solver, _ = build(
        3, 60_000, True, outer_seed=payload, relax=OUTER_ONLY_RELAX
    )
    assert solver.check() == sat

    blocks = [set(block) for block in BLOCKS]
    k_edges = {frozenset(edge) for edge in K_EDGES}

    def eligible(u, v):
        return u != v and not any(
            frozenset((a, b)) in k_edges
            for a in blocks[u] for b in blocks[v] if a != b
        )

    eligible_rows = [v for v in range(47) if eligible(SOURCE, v)]
    packings = [
        frozenset(rows) for rows in combinations(eligible_rows, 6)
        if all(not (blocks[u] & blocks[v]) for u, v in combinations(rows, 2))
    ]
    first_packings = [packing for packing in packings if FIRST in packing]
    second_packings = [packing for packing in packings if SECOND in packing]
    joint = [
        packing for packing in packings
        if FIRST in packing and SECOND in packing
    ]
    swaps = [
        (left, right) for left in first_packings for right in second_packings
        if SECOND not in left and FIRST not in right
        and left - {FIRST} == right - {SECOND}
    ]

    assert blocks[FIRST].isdisjoint(blocks[SECOND])
    assert len(eligible_rows) == 22
    assert len(packings) == 56
    assert len(first_packings) == 4
    assert len(second_packings) == 14
    assert not joint
    assert not swaps

    system = fixed_system(payload)
    local = {
        row: forced_local_packing_neighbors(system, row)
        for row in range(N)
    }
    infeasible = {
        row for row in range(N) if not local[row]["packing_count"]
    }
    obstructed = []
    for target in range(N):
        forced = {
            row for row in range(N)
            if target in local[row]["forced_neighbors"]
        }
        impossible = {
            row for row in range(N)
            if local[row]["packing_count"]
            and target not in local[row]["possible_neighbors"]
        }
        family = local_packing_family(system, target)
        if family and not any(
            forced <= packing and packing.isdisjoint(impossible)
            for packing in family
        ):
            obstructed.append(target)
    assert infeasible == {2, 4, 5, 25}
    assert obstructed == [43]
    assert contracted_residual_rows(system, 43, local) == [
        7, 18, 28, 29, 34, 38, 44
    ]

    first_witness = frozenset((15, 26, 38, 43, 44))
    second_witness = frozenset((5, 15, 26, 38, 44))
    source_family = local_packing_family(system, 18)
    assert first_witness in source_family
    assert second_witness in source_family
    assert first_witness - {43} == second_witness - {5}
    print("verified: pinned model satisfies retained branch-3 outer Q/K equations")
    print("verified: source 26 has 56 full size-six eligible packings")
    print("verified: rows 8 and 16 occur separately (4 and 14 packings)")
    print("verified: rows 8 and 16 have neither a joint packing nor one-swap core")
    print("verified: row 43 is the unique reverse-obstructed target")
    print("verified: source 18 swaps target 43 with infeasible row 5")


if __name__ == "__main__":
    main()
