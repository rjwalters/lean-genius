#!/usr/bin/env python3
"""Verify a branch-3 outer Q/K completion containing K3,3-wz."""

from itertools import combinations

from z3 import sat

from q9_b0_residual_defect_sat import build
from q9_symmetric_point_mass_obstruction import OUTER_ONLY_RELAX


BLOCKS = [
    [0, 8, 16], [1, 9, 17], [2, 10, 18], [3, 11, 19],
    [4, 12, 20], [5, 13, 21], [6, 14, 22], [7, 15, 23],
    [5, 9, 23], [6, 11, 16], [0, 13, 20], [2, 12, 22],
    [3, 10, 21], [7, 14, 17], [4, 8, 19], [1, 15, 18],
    [7, 13, 16], [0, 11, 23], [6, 9, 20], [4, 10, 22],
    [2, 15, 17], [5, 12, 19], [3, 8, 18], [1, 14, 21],
    [7, 8, 21], [3, 9, 16], [14, 19], [13, 23], [9, 22],
    [10, 16], [11, 17], [15, 20], [12, 18], [6, 21], [4, 17],
    [5, 18], [0, 22], [2, 23], [1, 19], [3, 20], [1, 13],
    [6, 15], [2, 8], [0, 10], [5, 14], [7, 12], [4, 11],
]

K_EDGES = [
    [0, 1], [0, 11], [0, 22], [1, 9], [1, 21], [2, 3],
    [2, 12], [2, 23], [3, 14], [3, 20], [4, 5], [4, 15],
    [4, 16], [5, 13], [5, 18], [6, 7], [6, 10], [6, 19],
    [7, 8], [7, 17], [8, 9], [8, 18], [9, 23], [10, 13],
    [10, 19], [11, 12], [11, 17], [12, 21], [13, 20],
    [14, 15], [14, 22], [15, 16], [16, 21], [17, 20],
    [18, 22], [19, 23],
]

CORE = {"w": 8, "a": 9, "b": 10, "z": 16, "c": 17, "d": 18}


def main():
    payload = {"branch": 3, "blocks": BLOCKS, "k_edges": K_EDGES}
    solver, _ = build(
        3, 60_000, True, outer_seed=payload, relax=OUTER_ONLY_RELAX
    )
    assert solver.check() == sat

    blocks = [set(block) for block in BLOCKS]
    left, right = {"w", "a", "b"}, {"z", "c", "d"}
    expected = {
        frozenset((u, v)) for u in left for v in right
        if {u, v} != {"w", "z"}
    }
    actual = {
        frozenset((u, v)) for u, v in combinations(CORE, 2)
        if blocks[CORE[u]] & blocks[CORE[v]]
    }
    assert actual == expected

    k_edges = {frozenset(edge) for edge in K_EDGES}

    def eligible(u, v):
        return u != v and not any(
            frozenset((a, b)) in k_edges
            for a in blocks[u] for b in blocks[v] if a != b
        )

    core_rows = set(CORE.values())
    assert not any(
        core_rows <= {v for v in range(47) if eligible(u, v)}
        for u in range(47)
    )
    print("verified: pinned model satisfies retained branch-3 outer Q/K equations")
    print("verified: rows 8,9,10 | 16,17,18 induce K3,3-wz")
    print("scope: this model has no source eligible to all six core rows")


if __name__ == "__main__":
    main()
