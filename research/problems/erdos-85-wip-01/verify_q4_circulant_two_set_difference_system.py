#!/usr/bin/env python3
"""Exhaust the two-color circulant strong-difference calibration over Z/8."""

from itertools import combinations


N = 8


def negate(two_set):
    return tuple(sorted((-value) % N for value in two_set))


def differences(left, right):
    return [(a - b) % N for a in left for b in right]


def main():
    two_sets = list(combinations(range(N), 2))
    inverse_pairs = sorted(
        {
            tuple(sorted((s, (-s) % N)))
            for s in range(N)
            if s != (-s) % N
        }
    )
    assert inverse_pairs == [(1, 7), (2, 6), (3, 5)]

    solutions = []
    for a00 in inverse_pairs:
        for a01 in two_sets:
            a10 = negate(a01)
            for a11 in inverse_pairs:
                routed = differences(a00, a10) + differences(a01, a11)
                if sorted(routed) == list(range(N)):
                    solutions.append((a00, a01, a11))

    assert len(solutions) == 32
    example = ((1, 7), (0, 1), (3, 5))
    assert example in solutions

    a00, a01, a11 = example
    a10 = negate(a01)
    first = set(differences(a00, a10))
    second = set(differences(a01, a11))
    assert first == {0, 1, 2, 7}
    assert second == {3, 4, 5, 6}
    assert first.isdisjoint(second) and first | second == set(range(N))

    print("q4 circulant two-set system: PASS (32 labeled solutions)")


if __name__ == "__main__":
    main()
