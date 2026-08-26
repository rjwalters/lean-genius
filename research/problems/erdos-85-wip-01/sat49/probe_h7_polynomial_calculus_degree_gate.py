#!/usr/bin/env python3
"""Build and validate the degree-three-visible subsystem of one H7 parent.

Polynomial calculus of degree at most three cannot use a quartic forbidden-C4
generator.  This probe keeps every degree/mask constraint and every C4
generator of degree at most two, then asks for a genuine satisfying model.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import subprocess
import tempfile
from pathlib import Path

import check_h7_t0_by_empty_graph as empty_graph
import check_h7_t0_canonical_compact as compact
import check_h7_t0_canonical_completion as canonical


def build_subsystem(
    edge_count: int, type_index: int
) -> tuple[
    compact.CompactCnf,
    dict[tuple[int, int], int],
    int,
    list[tuple[int, ...]],
]:
    cnf = compact.CompactCnf()
    edge_variables = {
        edge: cnf.variable() for edge in itertools.combinations(canonical.LOW, 2)
    }

    for vertex in canonical.LOW:
        incident = [
            variable for edge, variable in edge_variables.items() if vertex in edge
        ]
        support_card = (
            0
            if vertex in canonical.EMPTY
            else 1
            if vertex in canonical.SINGLETON
            else 2
        )
        cnf.exactly(incident, 7 - support_card)

    def status(left: int, right: int) -> bool | int:
        if left == right:
            return False
        edge = canonical.normalized_edge(left, right)
        if edge in canonical.FIXED_TRUE:
            return True
        return edge_variables.get(edge, False)

    quadratic: list[tuple[int, ...]] = []
    quartic_count = 0
    for left, right in itertools.combinations(canonical.VERTICES, 2):
        candidates = [
            vertex
            for vertex in canonical.VERTICES
            if vertex != left and vertex != right
        ]
        for first, second in itertools.combinations(candidates, 2):
            statuses = (
                status(left, first),
                status(right, first),
                status(left, second),
                status(right, second),
            )
            if False in statuses:
                continue
            variables = tuple(value for value in statuses if value is not True)
            if len(variables) == 2:
                cnf.add(*(-variable for variable in variables))
                quadratic.append(variables)
            else:
                assert len(variables) == 4
                quartic_count += 1

    representatives = empty_graph.graph_representatives(edge_count)
    if not 0 <= type_index < len(representatives):
        raise ValueError(f"type index must be below {len(representatives)}")
    mask = representatives[type_index]
    empty_graph.add_empty_cube(cnf, edge_variables, mask)

    assert len(quadratic) == 15680
    assert quartic_count == 671580
    return cnf, edge_variables, mask, quadratic


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--edge-count", type=int, choices=range(6, 10), default=6)
    parser.add_argument("--type-index", type=int, default=2)
    parser.add_argument("--solver", default="kissat")
    parser.add_argument("--time", type=int, default=60)
    parser.add_argument("--keep-cnf", type=Path)
    args = parser.parse_args()

    try:
        cnf, edge_variables, mask, quadratic = build_subsystem(
            args.edge_count, args.type_index
        )
    except ValueError as error:
        parser.error(str(error))
    if args.keep_cnf:
        path = args.keep_cnf
        temporary = None
    else:
        temporary = tempfile.TemporaryDirectory(prefix="h7-pc-degree-gate-")
        path = Path(temporary.name) / "subsystem.cnf"
    cnf.write(path)
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    print(f"variables={cnf.variable_count}")
    print(f"clauses={len(cnf.clauses)}")
    print(f"quadratic_c4={len(quadratic)}")
    print("quartic_c4_omitted=671580")
    print(f"sha256={digest}")

    completed = subprocess.run(
        [args.solver, "-q", f"--time={args.time}", str(path)],
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    positive = canonical.parse_assignment(completed.stdout)
    if positive is None:
        print(completed.stdout, end="")
        print("validated=NO_SAT_WITNESS")
        raise SystemExit(1)

    for vertex in canonical.LOW:
        support_card = (
            0
            if vertex in canonical.EMPTY
            else 1
            if vertex in canonical.SINGLETON
            else 2
        )
        assert (
            sum(
                variable in positive
                for edge, variable in edge_variables.items()
                if vertex in edge
            )
            == 7 - support_card
        )
    for index, (left, right) in enumerate(empty_graph.quotient.EDGES):
        variable = edge_variables[(7 + left, 7 + right)]
        assert (variable in positive) == bool((mask >> index) & 1)
    assert all(not all(variable in positive for variable in pair) for pair in quadratic)
    print("validated=SAT_DEGREE_MASK_PLUS_ALL_QUADRATIC_C4")
    if temporary is not None:
        temporary.cleanup()


if __name__ == "__main__":
    main()
