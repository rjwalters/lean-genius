#!/usr/bin/env python3
"""Verify a uniform integral factor ledger for NONBIP-CONNECTED.

This is a spectral/characteristic-polynomial control, not a graph.
"""

from __future__ import annotations

import sympy as sp


q = sp.symbols("q", integer=True, positive=True)

# Defect eigenvalues q-4 +/- 2 sqrt(2), each with multiplicity q/2.
capell_sum = q * (q - 4)
capell_square_sum = q * ((q - 4) ** 2 + 8)

residual = {
    q - 17: 1,                    # M-eigenvalue 16; choose adjacency root -4
    q - 2: 2,                     # M-eigenvalue 1; pair +/-1
    -(q - 2): 2,                  # M-eigenvalue 2q-3; even multiplicity
    -1: q**2 - 32 * q + 270,
    -2: 15 * q - 144,
    0: 16 * q - 132,
}


def verify_symbolically() -> None:
    residual_dim = sp.expand(sum(residual.values()))
    residual_sum = sp.expand(sum(mu * mult for mu, mult in residual.items()))
    residual_square_sum = sp.expand(
        sum(mu**2 * mult for mu, mult in residual.items())
    )

    assert sp.simplify(1 + q + residual_dim - q**2) == 0
    assert sp.simplify((q - 1) + capell_sum + residual_sum) == 0
    assert sp.simplify(
        (q - 1) ** 2 + capell_square_sum + residual_square_sum
        - q**2 * (q - 1)
    ) == 0

    x = sp.symbols("x")
    g = x**2 + 2 * x - 1
    assert sp.expand(g * g.subs(x, -x) - (x**4 - 6 * x**2 + 1)) == 0

    # g has multiplicity q/2-1 and g(-x) multiplicity 1.  Their trace is
    # -q+4, and the rational adjacency root -4 supplies the remainder.
    assert sp.simplify(-2 * (q / 2 - 2) - 4 + q) == 0


def verify_at(Q: int) -> None:
    assert Q >= 16 and Q & (Q - 1) == 0
    evaluate = lambda value: int(sp.sympify(value).subs(q, Q))
    values: dict[int, int] = {}
    for mu, mult in residual.items():
        evaluated_mu = evaluate(mu)
        values[evaluated_mu] = values.get(evaluated_mu, 0) + evaluate(mult)
    assert all(mult >= 0 for mult in values.values())
    assert values[Q - 17] % 2 == 1
    assert all(mult % 2 == 0 for mu, mult in values.items() if mu != Q - 17)
    assert max(values) < Q - 1  # the principal defect eigenvalue stays simple

    dim = 1 + Q + sum(values.values())
    trace = (Q - 1) + Q * (Q - 4) + sum(mu * mult for mu, mult in values.items())
    trace2 = (
        (Q - 1) ** 2
        + Q * ((Q - 4) ** 2 + 8)
        + sum(mu * mu * mult for mu, mult in values.items())
    )
    assert (dim, trace, trace2) == (Q * Q, 0, Q * Q * (Q - 1))
    print(f"q={Q} dim={dim} trace={trace} trace2={trace2} residual={values}")


if __name__ == "__main__":
    verify_symbolically()
    for Q in (16, 32, 64, 128, 256):
        verify_at(Q)
    print("verified: uniform integral Capell completion survives")
