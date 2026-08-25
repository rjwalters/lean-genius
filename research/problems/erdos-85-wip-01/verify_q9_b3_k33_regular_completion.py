#!/usr/bin/env python3
"""Verify the exact B.3 profile completion of the K3,3-wz exchange core."""

from itertools import combinations


TRIPLES = [
    (0, 0, 0), (0, 1, 3), (0, 2, 5), (0, 5, 1),
    (1, 0, 1), (1, 2, 2), (1, 3, 0), (1, 6, 6),
    (2, 0, 7), (2, 1, 1), (2, 2, 0), (2, 3, 4),
    (2, 4, 6), (3, 2, 7), (3, 3, 6), (3, 4, 0),
    (3, 6, 5), (4, 1, 6), (4, 2, 3), (4, 3, 1),
    (4, 4, 2), (5, 3, 7), (5, 6, 3), (6, 5, 5),
    (7, 4, 7), (7, 5, 6),
]

PAIRS = [
    (0, 1, 0, 4), (0, 1, 1, 7), (0, 1, 3, 7),
    (0, 1, 4, 6), (0, 1, 5, 0), (0, 1, 5, 5),
    (0, 1, 6, 6), (0, 2, 5, 4), (0, 2, 6, 1),
    (0, 2, 6, 2), (0, 2, 6, 4), (0, 2, 7, 0),
    (0, 2, 7, 2), (0, 2, 7, 3), (1, 2, 0, 4),
    (1, 2, 1, 2), (1, 2, 1, 5), (1, 2, 5, 3),
    (1, 2, 7, 4), (1, 2, 7, 5), (1, 2, 7, 7),
]

CORE_COORDS = {
    "w": (1, 2, 2),
    "a": (0, 0, 0),
    "b": (2, 1, 1),
    "z": (0, 1, 3),
    "c": (1, 0, 1),
    "d": (2, 2, 0),
}


def triple_block(t):
    return frozenset(enumerate(t))


def pair_block(p):
    g, h, i, j = p
    return frozenset(((g, i), (h, j)))


def main():
    blocks = [triple_block(t) for t in TRIPLES]
    blocks += [pair_block(p) for p in PAIRS]
    assert len(TRIPLES) == 26
    assert len(PAIRS) == 21
    assert len(blocks) == len(set(blocks)) == 47
    assert all(len(block) in (2, 3) for block in blocks)
    assert all(len({g for g, _ in block}) == len(block) for block in blocks)

    points = [(g, i) for g in range(3) for i in range(8)]
    degrees = {point: sum(point in block for block in blocks) for point in points}
    assert set(degrees.values()) == {5}
    assert all(len(left & right) <= 1 for left, right in combinations(blocks, 2))

    core = {name: triple_block(t) for name, t in CORE_COORDS.items()}
    assert all(block in blocks for block in core.values())
    left, right = {"w", "a", "b"}, {"z", "c", "d"}
    expected_edges = {
        frozenset((u, v)) for u in left for v in right
        if {u, v} != {"w", "z"}
    }
    actual_edges = {
        frozenset((u, v)) for u, v in combinations(core, 2)
        if core[u] & core[v]
    }
    assert actual_edges == expected_edges

    independent = []
    names = tuple(core)
    for size in range(1, len(names) + 1):
        for subset in combinations(names, size):
            if all(not (core[u] & core[v]) for u, v in combinations(subset, 2)):
                independent.append(frozenset(subset))
    alpha = max(map(len, independent))
    maximum = {subset for subset in independent if len(subset) == alpha}
    assert alpha == 3
    assert maximum == {frozenset(left), frozenset(right)}
    assert frozenset(("w", "z")) in independent
    assert not any(frozenset(("w", "z")) < subset for subset in independent)

    print("verified: 26 triples, 21 pairs, 24 point-degrees all five")
    print("verified: linear three-group profile and induced K3,3-wz core")
    print("verified: core maximum packings are exactly the two shores")


if __name__ == "__main__":
    main()
