#!/usr/bin/env python3
"""Prime-field controls for a uniform restricted-repair obstruction."""
from collections import Counter
from itertools import combinations


def check(q):
    # The selected q are primes. Uniform prime-power coverage is prose.
    vertices = ([(1, b, c) for b in range(q) for c in range(q)]
                + [(0, 1, c) for c in range(q)] + [(0, 0, 1)])
    def dot(x, y):
        return sum(a*b for a, b in zip(x, y)) % q
    absolute = {x for x in vertices if dot(x, x) == 0}
    retained = set(vertices)-absolute
    adjacency = {x: {y for y in retained if y != x and dot(x, y) == 0}
                 for x in retained}
    assert len(absolute) == q+1 and len(retained) == q*q
    assert all(len(adjacency[x] & adjacency[y]) <= 1
               for x, y in combinations(retained, 2))
    low = {x for x in retained if len(adjacency[x]) == q-1}
    high = retained-low
    assert len(low) == q*(q+1)//2 and len(high) == q*(q-1)//2
    assert all(len(adjacency[x]) == q+1 for x in high)
    assert all(len(adjacency[x] & high) == (q+1)//2 for x in high)
    assert all(len(adjacency[x] & high) == (q-1)//2 for x in low)
    reduced = {x: {y for y in adjacency[x] if not (x in high and y in high)}
               for x in retained}
    histogram = Counter()
    for x, y in combinations(low, 2):
        if y in reduced[x]:
            continue
        paths = [(u, w) for u in reduced[x] for w in reduced[u] & reduced[y]]
        assert all(len({x, u, w, y}) == 4 for u, w in paths)
        assert len(paths) >= (q-5)//2
        appearances = Counter(z for path in paths for z in path)
        assert max(appearances.values(), default=0) <= 2
        assert sum(count == 2 for count in appearances.values()) <= 1
        if q >= 17:
            assert len(paths)-(3+1) >= 1
        histogram[len(paths)] += 1
    assert histogram
    if q == 19:
        assert sum(histogram.values()) == 17100 and min(histogram) == 10
    mixed_count = 0
    for x in low:
        for y in high:
            # Only original nonedges can be newly added at L.
            if y in adjacency[x]:
                continue
            paths = [(u, w) for u in reduced[x] for w in reduced[u] & reduced[y]]
            assert all(len({x, u, w, y}) == 4 for u, w in paths)
            assert len(paths) >= (q-3)//2
            appearances = Counter(z for path in paths for z in path)
            assert max(appearances.values(), default=0) <= 2
            assert sum(count == 2 for count in appearances.values()) <= 1
            if q >= 17:
                assert len(paths)-(3+1) >= 1
            mixed_count += 1
    print(f'q={q}: {mixed_count} low-high nonedges PASS')
    print(f'q={q}: {sum(histogram.values())} low-low nonedges; '
          f'minimum remaining paths={min(histogram)}; exact checks PASS')


if __name__ == '__main__':
    for q in (5, 7, 13, 17, 19):
        check(q)
    print('All-three-deletions obstruction at q17 and q19 PASS; uniform proof is prose.')
    print('No exclusion of arbitrary graphs or other repair templates claimed.')
