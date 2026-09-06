#!/usr/bin/env python3
"""Exact characteristic-seven realization of the stored actual q=4 control.

The prose argument is in POLARITY_LOWER_DEGREE_DELETION_BARRIER.md.
This is a coordinate certificate, not a search over candidate graphs.
"""

from itertools import combinations
from math import gcd

from binary_q4_fixed_free_disconnected_control import A_EDGES, adjacency


def cross(x, y):
    return (x[1]*y[2]-x[2]*y[1], x[2]*y[0]-x[0]*y[2],
            x[0]*y[1]-x[1]*y[0])


def dot(x, y):
    return sum(a*b for a, b in zip(x, y))


def main():
    a = adjacency(A_EDGES)
    assert all(len(row) == 4 for row in a)
    assert all(len(a[i] & a[j]) <= 1 for i, j in combinations(range(16), 2))

    # These original columns force all four frame triples noncollinear,
    # even for embeddings that are allowed to add incidences.
    frame = (1, 3, 8, 9)
    pair_columns = {}
    for u, v in combinations(frame, 2):
        columns = [j for j in range(16) if {u, v} <= a[j]]
        assert len(columns) == 1
        pair_columns[u, v] = columns[0]
    assert len(set(pair_columns.values())) == 6

    points = {1: (1, 0, 0), 3: (0, 1, 0), 8: (0, 0, 1),
              9: (1, 1, 1)}
    lines = {}
    steps = []
    while True:
        changed = False
        for target, source, kind in ((lines, points, "line"),
                                     (points, lines, "point")):
            for i in range(16):
                if i in target:
                    continue
                pairs = list(combinations(sorted(a[i] & source.keys()), 2))
                if not pairs:
                    continue
                u, v = pairs[0]
                vector = cross(source[u], source[v])
                # No division or excluded-characteristic branch occurs.
                # Primitivity also means this vector stays nonzero in every
                # field, so each join/intersection is forced in every field.
                assert gcd(*vector) == 1
                target[i] = vector
                steps.append((kind, i, u, v, vector))
                changed = True
        if not changed:
            break
    assert len(points) == len(lines) == 16
    assert len(steps) == 28

    residuals = [dot(points[i], lines[j]) for i in range(16) for j in a[i]
                 if dot(points[i], lines[j])]
    assert len(residuals) == 8
    assert set(residuals) == {-7, 7}
    assert dot(points[6], lines[9]) == -7

    # Conversely these vectors give distinct points and distinct lines in
    # PG(2,7), with exactly the prescribed incidence matrix (strong embedding).
    for coordinates in (points, lines):
        assert all(any(x % 7 for x in v) for v in coordinates.values())
        assert all(any(x % 7 for x in cross(coordinates[i], coordinates[j]))
                   for i, j in combinations(range(16), 2))
    extra = [(i, j) for i in range(16) for j in range(16)
             if dot(points[i], lines[j]) % 7 == 0 and j not in a[i]]
    assert all(dot(points[i], lines[j]) % 7 == 0
               for i in range(16) for j in a[i])
    assert extra == []
    print("verified: actual q4 graph; six distinct frame sides")
    print("verified: 28 forced primitive integer joins/intersections")
    print("verified: eight incidence residuals are +/-7, forcing characteristic 7")
    print("verified: strong embedding in PG(2,7), hence every field of characteristic 7")
    for step in steps:
        print(step)


if __name__ == "__main__":
    main()
