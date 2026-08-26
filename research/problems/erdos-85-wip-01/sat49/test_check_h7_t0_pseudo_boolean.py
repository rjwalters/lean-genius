#!/usr/bin/env python3
"""Tests for the native pseudo-Boolean H7 parent emitter."""

from __future__ import annotations

import hashlib
import itertools
import tempfile
from pathlib import Path

import check_h7_t0_pseudo_boolean as target


def constraint_holds(terms, operator, rhs, assignment) -> bool:
    lhs = sum(coefficient * assignment[variable] for coefficient, variable in terms)
    return lhs >= rhs if operator == ">=" else lhs == rhs


def test_clause_translation() -> None:
    pb = target.PseudoBoolean()
    variables = [pb.variable() for _ in range(4)]
    pb.add(variables[0], -variables[1], variables[2], -variables[3])
    constraint = pb.constraints[0]
    for values in itertools.product((0, 1), repeat=4):
        assignment = dict(zip(variables, values))
        clause = bool(values[0] or not values[1] or values[2] or not values[3])
        assert constraint_holds(*constraint, assignment) == clause


def test_exact_translation() -> None:
    pb = target.PseudoBoolean()
    variables = [pb.variable() for _ in range(5)]
    pb.exactly(variables, 2)
    constraint = pb.constraints[0]
    for values in itertools.product((0, 1), repeat=5):
        assignment = dict(zip(variables, values))
        assert constraint_holds(*constraint, assignment) == (sum(values) == 2)


def test_full_parent_shape() -> None:
    pb, c4_count, empty_edges = target.build_parent(7, 2)
    assert pb.variable_count == 861
    assert c4_count == 687260
    assert len(empty_edges) == 7
    assert len(pb.constraints) == 687323
    assert sum(operator == "=" for _, operator, _ in pb.constraints) == 42
    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory) / "parent.opb"
        pb.write(path)
        header = path.open(encoding="ascii").readline()
        assert header == "* #variable= 861 #constraint= 687323 #equal= 42 intsize= 32\n"
        assert hashlib.sha256(path.read_bytes()).hexdigest() == (
            "c732895ad6badf109f2c50bb32d9ce108a5a76fec4779b3888023f6d2723bfc3"
        )


if __name__ == "__main__":
    test_clause_translation()
    test_exact_translation()
    test_full_parent_shape()
    print("ok")
