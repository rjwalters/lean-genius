#!/usr/bin/env python3
"""Verify the q=8 aggregate tetrahedron-residue triangle ledger."""

from itertools import combinations


Q = 8
COLORS = range(4)
PAIRS = list(combinations(COLORS, 2))
FACES = list(combinations(COLORS, 3))

# Every distinct-color face has odd count seven.
TRIPLE = {face: 7 for face in FACES}

# For i<j, MAJORITY[(i,j)] is P_iij.  The reverse P_ijj is 9-x.
MAJORITY = {
    (0, 1): 0,
    (0, 2): 7,
    (0, 3): 9,
    (1, 2): 0,
    (1, 3): 7,
    (2, 3): 5,
}


def majority(component: int, other: int) -> int:
    if component < other:
        return MAJORITY[(component, other)]
    return 9 - MAJORITY[(other, component)]


def main() -> None:
    # Every component pair has 4q cross edges.  A two-color triangle uses two
    # of them, and a distinct-color triangle using that pair uses one.
    for i, k in PAIRS:
        third_faces = [face for face in FACES if i in face and k in face]
        assert len(third_faces) == 2
        assert (
            2 * (majority(i, k) + majority(k, i))
            + sum(TRIPLE[face] for face in third_faces)
            == 4 * Q
        )

    selected_internal = {
        i: sum(majority(i, k) for k in COLORS if k != i)
        for i in COLORS
    }
    assert selected_internal == {0: 16, 1: 16, 2: 16, 3: 6}

    # Components 0,1,2 use a fully triangular C16.  Component 3 uses the C6
    # of a C6+C10 factor and leaves the C10 triangle-free.
    assert sum(selected_internal.values()) == 54
    assert sum(TRIPLE.values()) == 28
    cross_edges = len(PAIRS) * 4 * Q
    assert 2 * 54 + 3 * 28 == cross_edges == 192

    # Check the aggregate local matching capacities.  A vertex with both
    # internal neighbors used has two cross-cross triangle slots; one with
    # neither used has three.  The first three components have 16 used
    # vertices; the last has six used and ten unused.
    used_vertices = {0: 16, 1: 16, 2: 16, 3: 6}
    for i in COLORS:
        capacity = 2 * used_vertices[i] + 3 * (16 - used_vertices[i])
        distinct_incidence = sum(TRIPLE[f] for f in FACES if i in f)
        minority_incidence = sum(majority(k, i) for k in COLORS if k != i)
        assert distinct_incidence + minority_incidence == capacity

    assert all(value % 2 == 1 for value in TRIPLE.values())
    print("q8 tetrahedron triangle ledger: PASS")


if __name__ == "__main__":
    main()
