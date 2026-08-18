#!/usr/bin/env python3
"""Check the honest local owner-factorization CSP for the lambda-six blocks.

The input is ``lambda6_class_representatives.json``.  For every representative
this asks whether the whole complement of D can be partitioned into four
2-factors whose adjacency matrices commute with D.  In particular, it does
not assume that the distinguished spectral factor H is an owner color.

Requires the Python ``z3-solver`` package.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from time import monotonic

import z3


N = 16
COLORS = 4


def edge(u: int, v: int) -> tuple[int, int]:
    return (u, v) if u < v else (v, u)


def check_representative(name: str, record: dict[str, object]) -> z3.CheckSatResult:
    defect = {edge(*pair) for pair in record["D_edges"]}
    complement = [
        (u, v)
        for u in range(N)
        for v in range(u + 1, N)
        if (u, v) not in defect
    ]
    if len(defect) != 56 or len(complement) != 64:
        raise ValueError(f"{name}: expected |D|=56 and |D-complement|=64")

    edge_index = {pair: i for i, pair in enumerate(complement)}
    assigned = [
        [z3.Bool(f"{name}_color_{color}_edge_{i}") for i in range(64)]
        for color in range(COLORS)
    ]

    def color_edge(color: int, u: int, v: int) -> z3.BoolRef:
        if u == v or edge(u, v) not in edge_index:
            return z3.BoolVal(False)
        return assigned[color][edge_index[edge(u, v)]]

    def defect_entry(u: int, v: int) -> int:
        return int(u != v and edge(u, v) in defect)

    solver = z3.Solver()

    # The four owner colors uniquely partition every edge of D-complement.
    for i in range(64):
        solver.add(z3.PbEq([(assigned[color][i], 1) for color in range(COLORS)], 1))

    for color in range(COLORS):
        # Each restricted owner graph is a 2-factor.
        for u in range(N):
            incident = [
                (color_edge(color, u, v), 1)
                for v in range(N)
                if u != v and edge(u, v) in edge_index
            ]
            solver.add(z3.PbEq(incident, 2))

        # Entrywise A_color A_D = A_D A_color.
        for u in range(N):
            for v in range(N):
                left = z3.Sum(
                    [
                        z3.If(color_edge(color, u, w), defect_entry(w, v), 0)
                        for w in range(N)
                    ]
                )
                right = z3.Sum(
                    [
                        z3.If(color_edge(color, w, v), defect_entry(u, w), 0)
                        for w in range(N)
                    ]
                )
                solver.add(left == right)

    started = monotonic()
    result = solver.check()
    elapsed = monotonic() - started
    print(f"{name}: {result} ({elapsed:.3f}s)")
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("representatives", type=Path)
    args = parser.parse_args()
    data = json.loads(args.representatives.read_text())
    results = [check_representative(name, record) for name, record in data.items()]
    return 0 if all(result == z3.unsat for result in results) else 1


if __name__ == "__main__":
    raise SystemExit(main())
