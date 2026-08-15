#!/usr/bin/env python3
"""Regenerate the seven archived h=7, t=0 cube CNFs deterministically.

This is the recovered source of the August 10 deepsix-scout instances.  It
only emits DIMACS; solving and proof production are deliberately separate.
"""

import argparse
import hashlib
import itertools
from pathlib import Path

from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool


def build(cube: int) -> CNF:
    if cube not in range(7):
        raise ValueError("cube must be in 0..6")
    high_count, order = 7, 49
    highs = list(range(high_count))
    pool = IDPool()

    def edge(i: int, j: int) -> int:
        a, b = min(i, j), max(i, j)
        return pool.id(("e", a, b))

    clauses: list[list[int]] = []
    for a, b in itertools.combinations(highs, 2):
        clauses.append([-edge(a, b)])

    # Normalize N(0) and its induced perfect matching.
    n0 = list(range(7, 15))
    for x in range(7, order):
        clauses.append([edge(0, x)] if x in n0 else [-edge(0, x)])
    matching0 = {(7, 8), (9, 10), (11, 12), (13, 14)}
    for a, b in itertools.combinations(n0, 2):
        clauses.append([edge(a, b)] if (a, b) in matching0 else [-edge(a, b)])

    # Normalize N(1), its common vertex 7 with N(0), and its matching.
    n1 = [7] + list(range(15, 22))
    clauses.append([edge(1, 7)])
    for x in range(8, 15):
        clauses.append([-edge(1, x)])
    for x in range(15, 22):
        clauses.append([edge(1, x)])
    for x in range(22, order):
        clauses.append([-edge(1, x)])
    matching1 = {(7, 15), (16, 17), (18, 19), (20, 21)}
    for a, b in itertools.combinations(n1, 2):
        clauses.append([edge(a, b)] if (a, b) in matching1 else [-edge(a, b)])

    # Every high pair has a common low. C4-freeness supplies uniqueness.
    for i, j in itertools.combinations(highs, 2):
        common = []
        for w in range(high_count, order):
            aux = pool.id(("c", i, j, w))
            clauses.append([-aux, edge(i, w)])
            clauses.append([-aux, edge(j, w)])
            common.append(aux)
        clauses.append(common)

    for i, j in itertools.combinations(range(order), 2):
        others = [w for w in range(order) if w != i and w != j]
        for w, w2 in itertools.combinations(others, 2):
            clauses.append(
                [-edge(i, w), -edge(j, w), -edge(i, w2), -edge(j, w2)]
            )

    for vertex in range(order):
        incident = [edge(vertex, x) for x in range(order) if x != vertex]
        clauses.extend(
            CardEnc.equals(
                lits=incident,
                bound=8 if vertex < high_count else 7,
                vpool=pool,
                encoding=EncType.seqcounter,
            ).clauses
        )

    # The adjacency-partition law is instantiated for the two normalized codes.
    neighborhoods = {0: n0, 1: n1}
    for y in range(high_count, order):
        for w in (0, 1):
            clauses.append([edge(y, x) for x in neighborhoods[w] if x != y])

    # Cube on the unique N(1)-code neighbor of vertex 9.
    for index, member in enumerate(range(15, 22)):
        clauses.append([edge(9, member)] if index == cube else [-edge(9, member)])
    return CNF(from_clauses=clauses)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output_dir", type=Path)
    args = parser.parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    for cube in range(7):
        path = args.output_dir / f"h7t0_cube{cube}.cnf"
        build(cube).to_file(path)
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        print(f"{path.name}\t{digest}")


if __name__ == "__main__":
    main()
