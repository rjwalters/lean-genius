#!/usr/bin/env python3
"""Bounded compact-CNF probe for the no-triple three-high order-49 branch."""

from __future__ import annotations

import argparse
import hashlib
import itertools
import subprocess
import tempfile
from pathlib import Path

from check_h7_t0_canonical_compact import CompactCnf


PAIR01, PAIR02, PAIR12 = 0, 1, 2
UNIQUE0 = tuple(range(3, 9))
UNIQUE1 = tuple(range(9, 15))
UNIQUE2 = tuple(range(15, 21))
OUTSIDE = tuple(range(21, 46))
ORDINARY = tuple(range(46))
HIGH = (46, 47, 48)
VERTICES = ORDINARY + HIGH
CODES = (
    (PAIR01, PAIR02, *UNIQUE0),
    (PAIR01, PAIR12, *UNIQUE1),
    (PAIR02, PAIR12, *UNIQUE2),
)


def normalized_edge(left: int, right: int) -> tuple[int, int]:
    assert left != right
    return (left, right) if left < right else (right, left)


FIXED_TRUE = {
    normalized_edge(HIGH[h], ordinary) for h, code in enumerate(CODES) for ordinary in code
}


def support(vertex: int) -> int:
    return sum(vertex in code for code in CODES)


def canonical_matching(h: int, roots_adjacent: bool) -> tuple[tuple[int, int], ...]:
    roots = tuple(v for v in CODES[h] if support(v) == 2)
    unique = tuple(v for v in CODES[h] if support(v) == 1)
    if roots_adjacent:
        return ((roots[0], roots[1]), (unique[0], unique[1]),
                (unique[2], unique[3]), (unique[4], unique[5]))
    return ((roots[0], unique[0]), (roots[1], unique[1]),
            (unique[2], unique[3]), (unique[4], unique[5]))


def build_cnf(matching_profile: tuple[int, int, int] | None = None) -> tuple[
    CompactCnf, dict[tuple[int, int], int], int
]:
    cnf = CompactCnf()
    edge_variables = {
        edge: cnf.variable() for edge in itertools.combinations(ORDINARY, 2)
    }
    for vertex in ORDINARY:
        incident = [variable for edge, variable in edge_variables.items() if vertex in edge]
        cnf.exactly(incident, 7 - support(vertex))
    if matching_profile is not None:
        for h, bit in enumerate(matching_profile):
            for left, right in canonical_matching(h, bool(bit)):
                cnf.add(edge_variables[normalized_edge(left, right)])

    def status(left: int, right: int) -> bool | int:
        if left == right:
            return False
        edge = normalized_edge(left, right)
        if edge in FIXED_TRUE:
            return True
        return edge_variables.get(edge, False)

    c4_clauses = 0
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


def validate(edge_variables: dict[tuple[int, int], int], positive: set[int]) -> None:
    edges = set(FIXED_TRUE)
    edges.update(edge for edge, variable in edge_variables.items() if variable in positive)
    neighbors = [set() for _ in VERTICES]
    for left, right in edges:
        neighbors[left].add(right)
        neighbors[right].add(left)
    assert [len(neighbors[v]) for v in HIGH] == [8, 8, 8]
    assert all(len(neighbors[v]) == 7 for v in ORDINARY)
    for left, right in itertools.combinations(VERTICES, 2):
        assert len(neighbors[left] & neighbors[right]) <= 1


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--solver", default="kissat")
    parser.add_argument("--time", type=int, default=60)
    parser.add_argument("--keep-cnf", type=Path)
    parser.add_argument("--emit-only", action="store_true")
    parser.add_argument(
        "--matching-profile",
        choices=tuple("".join(map(str, bits)) for bits in itertools.product((0, 1), repeat=3)),
    )
    args = parser.parse_args()

    matching_profile = (
        tuple(map(int, args.matching_profile)) if args.matching_profile is not None else None
    )
    cnf, edge_variables, c4_clauses = build_cnf(matching_profile)
    if args.keep_cnf:
        path = args.keep_cnf
        temporary = None
    else:
        temporary = tempfile.TemporaryDirectory(prefix="order49-three-high-")
        path = Path(temporary.name) / "three-high.cnf"
    cnf.write(path)
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    print(f"edge_variables={len(edge_variables)}")
    print(f"variables={cnf.variable_count}")
    print(f"clauses={len(cnf.clauses)}")
    print(f"degree_clauses={len(cnf.clauses) - c4_clauses}")
    print(f"c4_clauses={c4_clauses}")
    print(f"sha256={digest}")
    if args.emit_only:
        if temporary is not None:
            temporary.cleanup()
        return 0
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
        print("validated_sat_model")
    if temporary is not None:
        temporary.cleanup()
    return 0 if completed.returncode in (10, 20) else 2


if __name__ == "__main__":
    raise SystemExit(main())
