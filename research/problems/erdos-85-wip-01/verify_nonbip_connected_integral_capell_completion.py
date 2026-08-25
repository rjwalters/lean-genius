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


def verify_uniform_cubic_completion() -> None:
    """Verify the stronger q >= 8 completion suggested by codex-sol-3."""
    a = q * (q - 1) / 4 - 2
    b = (q**2 - 22) / 6
    c = (q**2 - 3 * q - 16) / 12

    # The extra odd-dimensional P-orbit is zero-trace and real-rooted.
    x = sp.symbols("x")
    g3 = x**3 - 3 * x + 1
    h3_of_x2 = x**6 - 6 * x**4 + 9 * x**2 - 1
    assert sp.expand(g3 * g3.subs(x, -x) + h3_of_x2) == 0
    h3 = sp.Poly(sp.symbols("y") ** 3 - 6 * sp.symbols("y") ** 2
                 + 9 * sp.symbols("y") - 1)
    assert sp.Poly(g3, x).is_irreducible and h3.is_irreducible
    assert all(abs(complex(root).imag) < 1e-10 and 0 < complex(root).real < 4
               for root in h3.nroots())

    # Its three M-roots sum to 6 and have square-sum 18, hence the
    # corresponding three D-roots have these first two moments.
    cubic_defect_sum = 3 * q - 9
    cubic_defect_square_sum = 3 * q**2 - 18 * q + 33
    assert sp.simplify(1 + q + 3 + 2 * a + 2 * b + 2 * c + 10 - q**2) == 0
    assert sp.simplify(
        (q - 1) + capell_sum + cubic_defect_sum
        - 4 * a - 2 * b + 4 * c
    ) == 0
    assert sp.simplify(
        (q - 1) ** 2 + capell_square_sum + cubic_defect_square_sum
        + 8 * a + 2 * b + 8 * c
        - q**2 * (q - 1)
    ) == 0

    # A finite modular cycle proves integrality for every q=2^k, k>=3:
    # modulo 12, these powers alternate between 8 and 4.
    assert [pow(2, k, 12) for k in range(3, 11)] == [8, 4] * 4
    for k in range(3, 21):
        Q = 2**k
        exact_counts = [sp.factor(value.subs(q, Q)) for value in (a, b, c)]
        assert all(value.q == 1 for value in exact_counts)
        counts = [int(value) for value in exact_counts]
        assert all(value >= 0 for value in counts)
        assert Q + (Q // 2) * (-2) == 0
        if k <= 8:
            print(f"q={Q} cubic_completion_half_counts={counts}")


if __name__ == "__main__":
    verify_symbolically()
    verify_uniform_cubic_completion()
    for Q in (16, 32, 64, 128, 256):
        verify_at(Q)
    print("verified: uniform integral Capell completions survive")
