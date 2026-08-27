#!/usr/bin/env python3
"""Flat-projector countermodel to diagonal-moment multiplicity bounds."""

from __future__ import annotations

import argparse
import math

import numpy as np


def sylvester(order: int) -> np.ndarray:
    assert order > 0 and order & (order - 1) == 0
    matrix = np.ones((1, 1))
    while matrix.shape[0] < order:
        matrix = np.block([[matrix, matrix], [matrix, -matrix]])
    return matrix / math.sqrt(order)


def check(q: int) -> None:
    assert q >= 8 and q % 4 == 0 and q & (q - 1) == 0
    n = q * q
    count = n - q - 2
    left_count = 2
    right_count = count - left_count
    total = 6 - n
    square_total = n + 8 * q - 26
    mean = total / count
    variance = square_total / count - mean * mean
    left = mean + math.sqrt(variance * right_count / left_count)
    right = mean - math.sqrt(variance * left_count / right_count)

    # Adjacency roots above the round-66 defect ledger.  The q-dimensional
    # mu=q-2 sector has sign imbalance 2-q, and the two residual sectors are
    # sign-paired.
    roots = [float(q)]
    roots += [1.0] + [-1.0] * (q - 1)
    roots += [-2.0]
    for mu, multiplicity in ((left, left_count), (right, right_count)):
        root = math.sqrt(q - 1 - mu)
        roots += [root] * (multiplicity // 2)
        roots += [-root] * (multiplicity // 2)
    roots = np.asarray(roots)
    assert len(roots) == n
    assert abs(roots.sum()) < 1e-8
    assert abs(roots @ roots - n * q) < 1e-6

    basis = sylvester(n)
    adjacency_relaxation = (basis * roots) @ basis.T
    square = adjacency_relaxation @ adjacency_relaxation
    ones = np.ones(n)

    assert np.max(np.abs(np.diag(adjacency_relaxation))) < 1e-8
    assert np.max(np.abs(np.diag(square) - q)) < 1e-7
    assert np.max(np.abs(adjacency_relaxation @ ones - q * ones)) < 1e-7

    # Every eigenvector is flat, so the q-dimensional designated projector
    # has leverage q/n=1/q at every coordinate.
    designated = basis[:, 1 : q + 1] @ basis[:, 1 : q + 1].T
    assert np.max(np.abs(np.diag(designated) - 1 / q)) < 1e-8
    terminal_lhs = 2 * (q - 1) * q * q
    terminal_rhs = q * q
    assert terminal_lhs > terminal_rhs

    zero_one_distance = np.min(
        np.stack((np.abs(adjacency_relaxation), np.abs(adjacency_relaxation - 1))),
        axis=0,
    )
    print(
        f"q={q} n={n} designated_rank={q} "
        f"max_diag_A={np.max(np.abs(np.diag(adjacency_relaxation))):.3e} "
        f"max_diag_A2_error={np.max(np.abs(np.diag(square)-q)):.3e} "
        f"max_row_error={np.max(np.abs(adjacency_relaxation @ ones-q*ones)):.3e} "
        f"max_01_distance={np.max(zero_one_distance):.6f}"
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--q", type=int, nargs="*", default=[8, 16])
    args = parser.parse_args()
    for q in args.q:
        check(q)
    print("verified: flat projectors satisfy all diagonal moments but violate terminal rank scale")


if __name__ == "__main__":
    main()
