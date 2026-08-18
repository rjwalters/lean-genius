#!/usr/bin/env python3
"""Generate deterministic CNF for the all-triangle-free mu=3 grid code.

The formulas are the exact row/column-hit laws plus the C4 common-neighbour
bound used by ``mu3_alltf_grid_z3.py``.  Z3's ``pb2bv`` and ``tseitin-cnf``
tactics lower pseudo-Boolean constraints before DIMACS export; exporting a
raw Solver would incorrectly leave each PB constraint as an opaque atom.
"""

from __future__ import annotations

import argparse
from pathlib import Path

from z3 import And, Bool, Goal, PbEq, PbLe, Then


ORDER = 8


def internal_neighbours(shape: str) -> dict[int, set[int]]:
    if shape == "C16":
        return {i: {i, (i - 1) % 8} for i in range(8)}
    if shape == "C8C8":
        result: dict[int, set[int]] = {}
        for i in range(4):
            result[i] = {i, (i - 1) % 4}
            result[4 + i] = {4 + i, 4 + ((i - 1) % 4)}
        return result
    raise ValueError(f"unknown shape: {shape}")


def build_goal(shape: str) -> tuple[Goal, int, int]:
    nhx = internal_neighbours(shape)
    nhy = {j: {i for i in range(ORDER) if j in nhx[i]} for j in range(ORDER)}
    cells = [(i, j) for i in range(ORDER) for j in range(ORDER) if j not in nhx[i]]
    assert len(cells) == 48
    index = {cell: k for k, cell in enumerate(cells)}
    edges = {
        (a, b): Bool(f"e_{a}_{b}")
        for a in range(len(cells)) for b in range(a + 1, len(cells))
    }

    def edge(a: int, b: int):
        assert a != b
        return edges[(a, b) if a < b else (b, a)]

    goal = Goal()
    for u, (xu, yu) in enumerate(cells):
        for x in range(ORDER):
            terms = [edge(u, index[cell]) for cell in cells
                     if cell[0] == x and index[cell] != u]
            want = 0 if yu in nhx[x] else 1
            goal.add(PbEq([(term, 1) for term in terms], want))
        for y in range(ORDER):
            terms = [edge(u, index[cell]) for cell in cells
                     if cell[1] == y and index[cell] != u]
            want = 0 if xu in nhy[y] else 1
            goal.add(PbEq([(term, 1) for term in terms], want))

    for u in range(len(cells)):
        for v in range(u + 1, len(cells)):
            common = [And(edge(u, m), edge(v, m))
                      for m in range(len(cells)) if m not in (u, v)]
            goal.add(PbLe([(term, 1) for term in common], 1))
    return goal, len(cells), len(edges)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("shape", choices=("C16", "C8C8"))
    parser.add_argument("output", type=Path)
    args = parser.parse_args()

    goal, cells, edge_variables = build_goal(args.shape)
    lowered = Then("simplify", "pb2bv", "bit-blast", "tseitin-cnf")(goal)
    if len(lowered) != 1:
        raise RuntimeError(f"unexpected tactic result with {len(lowered)} goals")
    dimacs = lowered[0].dimacs()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(dimacs, encoding="ascii")
    header = next(line for line in dimacs.splitlines() if line.startswith("p cnf"))
    print(f"shape={args.shape} cells={cells} edge_variables={edge_variables} {header}")


if __name__ == "__main__":
    main()
