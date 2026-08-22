#!/usr/bin/env python3
"""Countermodels to spectral-only NONBIP-CONNECTED obstructions.

For even q >= 4, let D_q be the circulant on Z/(q^2) with generators

  q^2/2,  +/-1,  +/-2, +/-4, ..., +/-(q-4).

It is connected, nonbipartite, and (q-1)-regular.  Fourier modes j and
q^2-j have equal Laplacian eigenvalues.  The two unpaired modes give q^2
(the corrected principal eigenvalue) and 4 (the half-frequency Laplacian
eigenvalue), so

  charpoly(L(D_q) + J) = (x-q^2)(x-4) P_q(x)^2.

In particular det(L+J) is a square and the Matrix-Tree theorem makes the
spanning-tree number a square as well.  Thus the determinant identity and
even-multiplicity characteristic-polynomial tests do not exclude the
connected nonbipartite stratum, uniformly in binary q.

At q=4 and q=8 the exact factorization gives a sharper diagnostic.  Apart
from the principal root q^2 and the simple root 4, every irreducible factor
has nonsquare absolute constant term.  Hence its eigenvalue lambda is not a
square in Q(lambda): otherwise its field norm would be a square.  The sign
involution therefore makes that whole sector contribute zero to the trace
of any rational square root.  The only possible traces are q-2 and q+2,
not zero, so these two D_q do not admit an adjacency-matrix square root.

This trace refinement is deliberately asserted only for q=4,8.  The exact
SymPy calculation below is a finite regression of both statements.  q=16
remains supported for the spectral-only check, but the script makes no
uniform or q=16 claim about residual norms.
"""

from __future__ import annotations

import argparse
import math

import sympy as sp


def circulant_defect(q: int) -> sp.Matrix:
    assert q >= 4 and q % 2 == 0
    order = q * q
    positive_pairs = [1, *range(2, q - 2, 2)]
    generators = {order // 2}
    for step in positive_pairs:
        generators.update((step, order - step))
    assert len(generators) == q - 1
    adjacency = sp.zeros(order)
    for vertex in range(order):
        for step in generators:
            adjacency[vertex, (vertex + step) % order] = 1
    assert all(sum(adjacency.row(vertex)) == q - 1 for vertex in range(order))
    return adjacency


def verify(q: int) -> None:
    order = q * q
    adjacency = circulant_defect(q)
    # Step 1 connects the Cayley graph; the even involution q^2/2 gives an
    # edge inside a parity class, so the connected graph is nonbipartite.
    assert adjacency[0, 1] == 1 and adjacency[0, order // 2] == 1
    laplacian = (q - 1) * sp.eye(order) - adjacency
    corrected = laplacian + sp.ones(order)
    variable = sp.Symbol("x")
    characteristic = sp.Poly(corrected.charpoly(variable).as_expr(), variable)
    exceptional = sp.Poly((variable - order) * (variable - 4), variable)
    square_part = characteristic.exquo(exceptional)
    factors = sp.factor_list(square_part.as_expr())[1]
    assert all(exponent % 2 == 0 for _, exponent in factors)

    determinant = int(corrected.det())
    assert determinant > 0 and math.isqrt(determinant) ** 2 == determinant
    assert determinant % (order * order) == 0
    spanning_trees = determinant // (order * order)
    assert math.isqrt(spanning_trees) ** 2 == spanning_trees
    trace_suffix = ""
    if q in (4, 8):
        residual_norms = []
        for factor, exponent in sp.factor_list(characteristic.as_expr())[1]:
            polynomial = sp.Poly(factor, variable)
            if polynomial == sp.Poly(variable - order, variable):
                assert exponent == 1
                continue
            if polynomial == sp.Poly(variable - 4, variable):
                assert exponent == 1
                continue
            norm = abs(int(polynomial.TC()))
            assert math.isqrt(norm) ** 2 != norm
            assert exponent % 2 == 0
            residual_norms.append(norm)
        trace_candidates = (q - 2, q + 2)
        assert all(candidate != 0 for candidate in trace_candidates)
        trace_suffix = (
            f" residual_norms={residual_norms} "
            f"square_root_trace_candidates={list(trace_candidates)} "
            "zero_trace_impossible=true"
        )
    print(
        f"q={q} order={order} degree={q - 1} connected=true nonbipartite=true "
        f"corrected_charpoly=(x-{order})(x-4)P^2 "
        f"det_square=true spanning_trees_square=true{trace_suffix}"
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("q", nargs="*", type=int, default=[4, 8])
    args = parser.parse_args()
    for q in args.q:
        verify(q)
    print(f"verified_connected_spectral_countermodels={len(args.q)}")


if __name__ == "__main__":
    main()
