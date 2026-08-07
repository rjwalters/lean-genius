#!/usr/bin/env python3
"""Enumerate h=1 branch-miss tables up to the natural CP4 symmetry.

For a profile word in {A,B}^4, an A mate-pair has matched counts (2,4)
and a B mate-pair has matched counts (4,4).  A miss table is a symmetric
8-by-8 nonnegative integer matrix, supported away from the diagonal and the
four mate edges, whose row sums are those matched counts.

With ``--even``, divide every entry and row sum by two.  This is the reduced
table problem that results if every internal matched pair has a common miss
label.  Multiplying the printed representative entries by two recovers the
original miss counts.
"""

import argparse
import itertools


MATE = (1, 0, 3, 2, 5, 4, 7, 6)
EDGES = tuple(
    (i, j)
    for i in range(8)
    for j in range(i + 1, 8)
    if MATE[i] != j
)
EDGE_INDEX = {edge: k for k, edge in enumerate(EDGES)}


def cp4_automorphisms():
    """The wreath product C2^4 semidirect S4, of order 384."""
    for pair_permutation in itertools.permutations(range(4)):
        for flips in itertools.product(range(2), repeat=4):
            yield tuple(
                2 * pair_permutation[i // 2] + ((i % 2) ^ flips[i // 2])
                for i in range(8)
            )


def profile_rows(profile, even_only):
    rows = []
    for kind in profile:
        rows.extend((2, 4) if kind == "A" else (4, 4))
    return tuple(row // 2 for row in rows) if even_only else tuple(rows)


def enumerate_tables(rows):
    solutions = set()
    degree = [0] * 8
    values = [0] * len(EDGES)

    def visit(k):
        if k == len(EDGES):
            if tuple(degree) == rows:
                solutions.add(tuple(values))
            return
        i, j = EDGES[k]
        upper = min(rows[i] - degree[i], rows[j] - degree[j])
        for value in range(upper + 1):
            values[k] = value
            degree[i] += value
            degree[j] += value
            if all(degree[a] <= rows[a] for a in range(8)):
                visit(k + 1)
            degree[i] -= value
            degree[j] -= value
        values[k] = 0

    visit(0)
    return solutions


def transform(table, permutation):
    result = [0] * len(EDGES)
    for k, (i, j) in enumerate(EDGES):
        image = tuple(sorted((permutation[i], permutation[j])))
        result[EDGE_INDEX[image]] = table[k]
    return tuple(result)


def orbit_representatives(tables, automorphisms):
    remaining = set(tables)
    representatives = []
    while remaining:
        representative = min(remaining)
        remaining.difference_update(
            transform(representative, permutation)
            for permutation in automorphisms
        )
        representatives.append(representative)
    return representatives


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("profile", choices=("AAAA", "AAAB", "AABB", "ABBB", "BBBB"))
    parser.add_argument("--even", action="store_true", dest="even_only")
    parser.add_argument("--show-representatives", action="store_true")
    args = parser.parse_args()

    rows = profile_rows(args.profile, args.even_only)
    automorphisms = tuple(
        permutation
        for permutation in cp4_automorphisms()
        if all(rows[permutation[i]] == rows[i] for i in range(8))
    )
    tables = enumerate_tables(rows)
    representatives = orbit_representatives(tables, automorphisms)
    support_histogram = {}
    for table in representatives:
        support = sum(value != 0 for value in table)
        support_histogram[support] = support_histogram.get(support, 0) + 1

    mode = "even" if args.even_only else "unrestricted"
    print(f"profile={args.profile} mode={mode}")
    print(f"rows={rows}")
    print(f"stabilizer_order={len(automorphisms)}")
    print(f"labeled_tables={len(tables)}")
    print(f"orbits={len(representatives)}")
    print(f"support_histogram={sorted(support_histogram.items())}")
    if args.show_representatives:
        scale = 2 if args.even_only else 1
        for index, table in enumerate(representatives):
            support = [
                (EDGES[k], scale * value)
                for k, value in enumerate(table)
                if value
            ]
            print(index, support)


if __name__ == "__main__":
    main()
