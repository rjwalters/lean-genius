#!/usr/bin/env python3
"""Emit and solve the single canonical H7/T0 completion instance.

Vertex order is stable and matches the formal H7 indexing bridge:

* 0..6: high vertices;
* 7..13: empty-support low vertices;
* 14..27: singleton vertices, ``14 + 2*label + copy``;
* 28..48: pair vertices in lexicographic ``combinations(range(7), 2)`` order.

Only the 861 low-low edges are variables, ordered lexicographically by their
endpoint pair.  The high-high and high-empty edges are fixed false; the
high-singleton and high-pair edges are the canonical support pattern.  The
CNF requires low degrees E=7, S=6, P=5 and at most one common neighbor for
every pair of the 49 canonical vertices.  Exact cardinalities use a stable
Sinz sequential-counter encoding.  Thus SAT is a genuine H7/T0 graph, while
certified UNSAT eliminates the entire H7/T0 stratum once replayed against the
formal ``SevenHighT0CanonicalCompletionSemantics`` bridge.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import subprocess
import tempfile
from pathlib import Path


HIGH = tuple(range(7))
EMPTY = tuple(range(7, 14))
SINGLETON = tuple(range(14, 28))
PAIR = tuple(range(28, 49))
LOW = EMPTY + SINGLETON + PAIR
VERTICES = HIGH + LOW
LABEL_PAIRS = tuple(itertools.combinations(range(7), 2))
EXPECTED_SHA256 = "31a550a04f2369b4f0e8d70a9ac3d0be448017505b80db1e58a983bc8a4228a9"


def normalized_edge(left: int, right: int) -> tuple[int, int]:
    assert left != right
    return (left, right) if left < right else (right, left)


FIXED_TRUE = {
    normalized_edge(copy // 2, 14 + copy) for copy in range(14)
} | {
    normalized_edge(label, 28 + index)
    for index, labels in enumerate(LABEL_PAIRS)
    for label in labels
}


class Cnf:
    def __init__(self) -> None:
        self.variable_count = 0
        self.clauses: list[tuple[int, ...]] = []

    def variable(self) -> int:
        self.variable_count += 1
        return self.variable_count

    def add(self, *literals: int) -> None:
        self.clauses.append(tuple(literals))

    def at_most(self, literals: list[int], bound: int) -> None:
        """Stable Sinz counter for ``sum(literals) <= bound``."""
        size = len(literals)
        assert 0 < bound < size
        counter = [
            [self.variable() for _ in range(bound)] for _ in range(size)
        ]
        self.add(-literals[0], counter[0][0])
        for column in range(1, bound):
            self.add(-counter[0][column])
        for row in range(1, size):
            self.add(-literals[row], counter[row][0])
            self.add(-counter[row - 1][0], counter[row][0])
            for column in range(1, bound):
                self.add(
                    -literals[row],
                    -counter[row - 1][column - 1],
                    counter[row][column],
                )
                self.add(-counter[row - 1][column], counter[row][column])
            self.add(-literals[row], -counter[row - 1][bound - 1])

    def exactly(self, literals: list[int], target: int) -> None:
        assert 0 < target < len(literals)
        self.at_most(literals, target)
        self.at_most([-literal for literal in literals], len(literals) - target)

    def write(self, path: Path) -> None:
        with path.open("w", encoding="ascii") as handle:
            handle.write(f"p cnf {self.variable_count} {len(self.clauses)}\n")
            for clause in self.clauses:
                handle.write(" ".join(map(str, clause)) + " 0\n")


def build_cnf(cnf_factory=Cnf) -> tuple[Cnf, dict[tuple[int, int], int], int]:
    cnf = cnf_factory()
    edge_variables = {
        edge: cnf.variable() for edge in itertools.combinations(LOW, 2)
    }

    for vertex in LOW:
        incident = [
            variable for edge, variable in edge_variables.items() if vertex in edge
        ]
        support_card = 0 if vertex in EMPTY else 1 if vertex in SINGLETON else 2
        cnf.exactly(incident, 7 - support_card)

    def status(left: int, right: int) -> bool | int:
        if left == right:
            return False
        edge = normalized_edge(left, right)
        if edge in FIXED_TRUE:
            return True
        return edge_variables.get(edge, False)

    c4_clauses = 0
    # Deterministic order: endpoint pair, then candidate-common-neighbor pair.
    for left, right in itertools.combinations(VERTICES, 2):
        candidates = [v for v in VERTICES if v != left and v != right]
        for first, second in itertools.combinations(candidates, 2):
            statuses = (
                status(left, first),
                status(right, first),
                status(left, second),
                status(right, second),
            )
            if False in statuses:
                continue
            cnf.add(*(-value for value in statuses if value is not True))
            c4_clauses += 1
    return cnf, edge_variables, c4_clauses


def parse_assignment(output: str) -> set[int] | None:
    if "s SATISFIABLE" not in output:
        return None
    return {
        int(token)
        for line in output.splitlines()
        if line.startswith("v ")
        for token in line[2:].split()
        if int(token) > 0
    }


def validate(
    edge_variables: dict[tuple[int, int], int], positive: set[int]
) -> None:
    edges = set(FIXED_TRUE)
    edges.update(edge for edge, variable in edge_variables.items() if variable in positive)
    neighbors = [set() for _ in VERTICES]
    for left, right in edges:
        neighbors[left].add(right)
        neighbors[right].add(left)
    assert [len(neighbors[v]) for v in HIGH] == [8] * 7
    assert [len(neighbors[v]) for v in LOW] == [7] * 7 + [6] * 14 + [5] * 21
    for left, right in itertools.combinations(VERTICES, 2):
        assert len(neighbors[left] & neighbors[right]) <= 1


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--solver", default="kissat")
    parser.add_argument("--time", type=int, default=1800)
    parser.add_argument("--keep-cnf", type=Path)
    parser.add_argument("--emit-only", action="store_true")
    args = parser.parse_args()

    cnf, edge_variables, c4_clauses = build_cnf()
    assert len(edge_variables) == 861
    assert cnf.variable_count == 71463
    assert c4_clauses == 687260
    assert len(cnf.clauses) == 830102
    if args.keep_cnf:
        path = args.keep_cnf
        temporary = None
    else:
        temporary = tempfile.TemporaryDirectory(prefix="h7-canonical-")
        path = Path(temporary.name) / "canonical.cnf"
    cnf.write(path)
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    assert digest == EXPECTED_SHA256
    print(f"edge_variables={len(edge_variables)}")
    print(f"variables={cnf.variable_count}")
    print(f"clauses={len(cnf.clauses)}")
    print(f"degree_clauses={len(cnf.clauses) - c4_clauses}")
    print(f"c4_clauses={c4_clauses}")
    print(f"sha256={digest}")
    print(f"cnf={path}")
    if args.emit_only:
        if temporary is not None:
            temporary.cleanup()
        return
    completed = subprocess.run(
        [args.solver, "-q", f"--time={args.time}", str(path)],
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    print(completed.stdout, end="")
    positive = parse_assignment(completed.stdout)
    if positive is not None:
        validate(edge_variables, positive)
        print("validated=SAT_GENUINE_H7_T0_GRAPH")
    elif "s UNSATISFIABLE" in completed.stdout:
        print("validated=UNSAT_CANONICAL_H7_T0_VERDICT_ONLY")
    else:
        print("validated=UNKNOWN")
    if temporary is not None:
        temporary.cleanup()


if __name__ == "__main__":
    main()
