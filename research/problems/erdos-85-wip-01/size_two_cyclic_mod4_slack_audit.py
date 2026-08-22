#!/usr/bin/env python3
"""Exact modulo-four disjoint-pair and two-walk slack census."""

from argparse import ArgumentParser
from collections import Counter
from itertools import combinations


def cls(delta: int) -> int:
    residue = delta % 4
    return min(residue, (-residue) % 4)


def audit(q: int, a: int) -> None:
    holes = {a % q, (-1 - a) % q}
    cells = [(x, y) for x in range(q) for y in range(q)
             if (y - x) % q not in holes]
    disjoint = Counter()
    for first, second in combinations(cells, 2):
        if first[0] != second[0] and first[1] != second[1]:
            disjoint[cls(second[0] - first[0])] += 1

    wedges = Counter()
    directed_edges = Counter()
    for x, y in cells:
        t = (y - x) % q
        rows = [r for r in range(q) if r not in {t, (t + 1) % q}]
        for row in rows:
            directed_edges[cls(row)] += 1
        for left, right in combinations(rows, 2):
            wedges[cls(right - left)] += 1

    slack = {kind: disjoint[kind] - wedges[kind] for kind in (0, 1, 2)}
    edges = {kind: directed_edges[kind] // 2 for kind in (0, 1, 2)}
    print(f"q={q} a={a}: disjoint={dict(disjoint)} wedges={dict(wedges)} "
          f"edges={edges} slack={slack}")


if __name__ == "__main__":
    parser = ArgumentParser()
    parser.add_argument("q", type=int)
    parser.add_argument("a", type=int, nargs="+")
    args = parser.parse_args()
    for a in args.a:
        audit(args.q, a)
