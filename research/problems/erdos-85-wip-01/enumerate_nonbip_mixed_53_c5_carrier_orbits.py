#!/usr/bin/env python3
"""Enumerate the finite C5 carrier normal forms modulo dihedral symmetry."""

from __future__ import annotations

import hashlib
import itertools
import json
from collections import Counter


N = 5


def transform_pair(h: tuple[int, ...], r: tuple[int, ...], shift: int,
                   reflected: bool
                   ) -> tuple[tuple[int, ...], tuple[int, ...]]:
    if not reflected:
        return (tuple(h[(i + shift) % N] for i in range(N)),
                tuple(r[(i + shift) % N] for i in range(N)))
    # h_i labels {i,i+1}, whereas r_i labels the chord {i,i+2}; reflection
    # therefore shifts the two coordinate systems by different offsets.
    return (tuple(h[(shift - i - 1) % N] for i in range(N)),
            tuple(r[(shift - i - 2) % N] for i in range(N)))


def orbit(h: tuple[int, ...], r: tuple[int, ...]
          ) -> set[tuple[tuple[int, ...], tuple[int, ...]]]:
    return {transform_pair(h, r, shift, reflected)
            for reflected in (False, True) for shift in range(N)}


def canonical(h: tuple[int, ...], r: tuple[int, ...]
              ) -> tuple[tuple[int, ...], tuple[int, ...]]:
    return min(orbit(h, r))


def valid(h: tuple[int, ...], r: tuple[int, ...]) -> bool:
    # r_i=1 means S_i intersects S_(i+2).  Two consecutive ambient cycle
    # edges h_i=h_(i+1)=1 already supply the unique common neighbor, so that
    # exterior intersection is forbidden.
    return all(not r[i] or not (h[i] and h[(i + 1) % N]) for i in range(N))


def main() -> None:
    labeled = []
    for h in itertools.product((0, 1), repeat=N):
        for r in itertools.product((0, 1), repeat=N):
            if valid(h, r):
                labeled.append((h, r))
    representatives = sorted({canonical(h, r) for h, r in labeled})

    # Every valid labeled form belongs to exactly one listed orbit, and every
    # transform preserves the common-neighbor exclusion.
    assert all(valid(h, r) for h, r in representatives)
    covered = set().union(*(orbit(h, r) for h, r in representatives))
    assert covered == set(labeled)

    census = Counter()
    for h, r in representatives:
        adjacent_pairs = sum(h[i] * h[(i + 1) % N] for i in range(N))
        doubles = sum(r)
        assert doubles <= N - adjacent_pairs
        census[(sum(h), adjacent_pairs, doubles)] += 1

    serialized = json.dumps(representatives, separators=(",", ":")).encode()
    print(json.dumps({
        "dihedral_orbits": len(representatives),
        "labeled_forms": len(labeled),
        "representatives_sha256": hashlib.sha256(serialized).hexdigest(),
        "stratum_count": len(census),
    }, sort_keys=True))


if __name__ == "__main__":
    main()
