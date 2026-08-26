#!/usr/bin/env python3
"""Test the binary characteristic-square module on one H7 relaxation model."""

from __future__ import annotations

import argparse
import hashlib
import subprocess
import tempfile
from pathlib import Path

import sympy

import check_h7_t0_by_empty_graph as empty_graph
import check_h7_t0_canonical_completion as canonical
import probe_h7_polynomial_calculus_degree_gate as degree_gate


def gf2_rank(rows: list[int], columns: int) -> int:
    work = list(rows)
    rank = 0
    for column in range(columns):
        pivot = next(
            (row for row in range(rank, len(work)) if (work[row] >> column) & 1),
            None,
        )
        if pivot is None:
            continue
        work[rank], work[pivot] = work[pivot], work[rank]
        for row in range(len(work)):
            if row != rank and ((work[row] >> column) & 1):
                work[row] ^= work[rank]
        rank += 1
    return rank


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--solver", default="kissat")
    parser.add_argument("--time", type=int, default=60)
    args = parser.parse_args()

    cnf, edge_variables, mask, quadratic = degree_gate.build_subsystem(6, 2)
    with tempfile.TemporaryDirectory(prefix="h7-f4-module-") as directory:
        path = Path(directory) / "relaxation.cnf"
        cnf.write(path)
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        completed = subprocess.run(
            [args.solver, "-q", f"--time={args.time}", str(path)],
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            check=False,
        )
    positive = canonical.parse_assignment(completed.stdout)
    assert positive is not None

    for vertex in canonical.LOW:
        support = (
            0
            if vertex in canonical.EMPTY
            else 1
            if vertex in canonical.SINGLETON
            else 2
        )
        assert sum(
            variable in positive
            for edge, variable in edge_variables.items()
            if vertex in edge
        ) == 7 - support
    for position, (left, right) in enumerate(empty_graph.quotient.EDGES):
        variable = edge_variables[(7 + left, 7 + right)]
        assert (variable in positive) == bool((mask >> position) & 1)
    assert all(not all(variable in positive for variable in pair) for pair in quadratic)

    low = list(canonical.LOW)
    index = {vertex: position for position, vertex in enumerate(low)}
    rows = [0] * len(low)
    exact = sympy.zeros(len(low))
    for (left, right), variable in edge_variables.items():
        if variable not in positive:
            continue
        i, j = index[left], index[right]
        rows[i] |= 1 << j
        rows[j] |= 1 << i
        exact[i, j] = exact[j, i] = 1

    polynomial_rows = []
    for i, row in enumerate(rows):
        square_row = 0
        for neighbor in range(len(low)):
            if (row >> neighbor) & 1:
                square_row ^= rows[neighbor]
        polynomial_rows.append(square_row ^ row ^ (1 << i))
    rank = gf2_rank(polynomial_rows, len(low))
    nullity = len(low) - rank

    all_ones = (1 << len(low)) - 1
    singleton_indicator = sum(
        1 << index[vertex] for vertex in canonical.SINGLETON
    )
    assert all((row & all_ones).bit_count() % 2 == 0 for row in polynomial_rows)
    assert all(
        (row & singleton_indicator).bit_count() % 2 == 0
        for row in polynomial_rows
    )
    assert nullity == 2

    coefficients = [int(value) for value in exact.charpoly().all_coeffs()]
    assert all(coefficient % 2 == 0 for position, coefficient in enumerate(coefficients) if position % 2)

    print(f"relaxation_sha256={digest}")
    print("validated=SAT_DEGREE_MASK_PLUS_ALL_QUADRATIC_C4")
    print("charpoly_mod2_is_square=true")
    print(f"rank_C2_plus_C_plus_I_mod2={rank}")
    print(f"kernel_dimension={nullity}")
    print("kernel_exactly_fixed_span=true")
    print(f"fixed_weights={singleton_indicator.bit_count()},{all_ones.bit_count()}")


if __name__ == "__main__":
    main()
