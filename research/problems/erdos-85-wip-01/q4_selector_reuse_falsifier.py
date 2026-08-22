#!/usr/bin/env python3
"""Falsify the q=4 global selector-reuse local-flag formula.

Exploratory only: these are external SAT signals, not certificates.  Any bad
defect two-path can be relabelled ``1-0-2``, so the first query is exhaustive
over loopless symmetric 4-regular C4-free graphs on 16 vertices.  The second
query additionally imposes the banked control's global defect split [8,8]
and asks only for a parity violation.  Both are SAT: the formula observed on
one exact q=4 control is not a square-order or [8,8]-partition identity.
"""

from __future__ import annotations

import subprocess
import tempfile
from itertools import combinations
from pathlib import Path

from z3 import And, Bool, Goal, If, Not, Or, SolverFor, Sum, Then

Q = 4
N = Q * Q


def solve(*, parity_only: bool, split_eight_eight: bool) -> tuple[str, str]:
    solver = SolverFor("QF_FD")
    edge = {(i, j): Bool(f"a_{i}_{j}") for i, j in combinations(range(N), 2)}

    def adj(i: int, j: int):
        return False if i == j else edge[min(i, j), max(i, j)]

    common = {}
    for i, j in combinations(range(N), 2):
        common[i, j] = Sum([
            If(And(adj(i, k), adj(j, k)), 1, 0)
            for k in range(N) if k not in (i, j)
        ])
        solver.add(common[i, j] <= 1)
    for i in range(N):
        solver.add(Sum([
            If(adj(i, j), 1, 0) for j in range(N) if j != i
        ]) == Q)

    def common_count(i: int, j: int):
        return common[min(i, j), max(i, j)]

    def defect(i: int, j: int):
        return common_count(i, j) == 0

    def triangle_free(i: int, j: int):
        return And(adj(i, j), defect(i, j))

    def selector(i: int, j: int):
        return False if i == j else And(Not(adj(i, j)), common_count(i, j) == 1)

    # Lossless bad-path normalization.
    solver.add(defect(1, 0), defect(0, 2))
    if split_eight_eight:
        for i in range(8):
            for j in range(8, 16):
                solver.add(Not(defect(i, j)))
        # Lossless rooted-spanning-tree normalization inside both components.
        for v in list(range(1, 8)) + list(range(9, 16)):
            start = 0 if v < 8 else 8
            solver.add(Or(*[defect(u, v) for u in range(start, v)]))

    reuse = Sum([
        If(And(selector(1, z), selector(0, z), selector(2, z)), 1, 0)
        for z in range(N)
    ])
    proposed = (
        2 + If(adj(1, 2), 1, 0)
        + If(triangle_free(1, 0) != triangle_free(0, 2), 2, 0)
    )
    if parity_only:
        solver.add(Or(*[
            And(reuse == i, proposed == j)
            for i in range(N + 1) for j in range(2, 6) if (i - j) % 2
        ]))
    else:
        solver.add(reuse != proposed)

    goal = Goal()
    goal.add(*solver.assertions())
    dimacs = Then(
        "simplify", "solve-eqs", "lia2card", "card2bv",
        "bit-blast", "tseitin-cnf",
    )(goal)[0].dimacs()
    with tempfile.TemporaryDirectory(prefix="q4-selector-") as directory:
        path = Path(directory) / "query.cnf"
        path.write_text(dimacs)
        process = subprocess.run(
            ["kissat", "--time=300", str(path)],
            text=True, capture_output=True, check=False,
        )
    status = next(
        (line[2:] for line in process.stdout.splitlines() if line.startswith("s ")),
        "UNKNOWN",
    )
    return dimacs.splitlines()[0], status


def main() -> None:
    queries = [
        ("exact_local_formula", False, False),
        ("parity_with_connected_8_8_split", True, True),
    ]
    for name, parity_only, split in queries:
        header, status = solve(parity_only=parity_only, split_eight_eight=split)
        print(f"{name}: {status}; {header}")


if __name__ == "__main__":
    main()
