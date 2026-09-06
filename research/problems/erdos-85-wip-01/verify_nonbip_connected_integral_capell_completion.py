#!/usr/bin/env python3
"""Verify a uniform integral factor ledger for NONBIP-CONNECTED.

This is a spectral/characteristic-polynomial control, not a graph.
The cubic completion fails triangle-trace parity; the older rational-root
completion passes that necessary condition. Neither is a graph witness.
The older completion fails the integer regular-matrix Hoffman divisibility
condition, uniformly for binary q >= 16.
"""

from __future__ import annotations

import sympy as sp
import runpy
from pathlib import Path


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


def verify_graph_parity_scope() -> None:
    """Separate the advertised defect moments from extra graph constraints."""
    x = sp.symbols("x")
    g = sp.Poly(x**2 + 2*x - 1, x)
    h = sp.Poly(x**3 - 3*x + 1, x)
    # Exact Newton sums, computed by multiplication in each quotient ring.
    def power_trace(poly: sp.Poly, power: int) -> sp.Expr:
        degree = poly.degree()
        multiplication = sp.zeros(degree)
        for column in range(degree):
            remainder = sp.rem(sp.Poly(x**(column+1), x), poly)
            for row in range(degree):
                multiplication[row, column] = remainder.nth(row)
        return sp.trace(multiplication**power)

    assert power_trace(g, 3) == -14
    assert power_trace(h, 3) == -3
    cubic_trace = sp.expand(q**3 + q/2 * power_trace(g, 3)
                            + power_trace(h, 3))
    older_trace = sp.expand(q**3 + (q/2-2) * power_trace(g, 3) - 4**3)
    assert cubic_trace == q**3 - 7*q - 3
    assert older_trace == q**3 - 7*q - 36
    # Mod 2, paired-root factors are squares. In the cubic completion the
    # remaining principal factor x times h has derivative 1, not zero.
    assert sp.Poly(sp.diff(x*h.as_expr(), x), x, modulus=2).as_expr() == 1
    # In the older completion the principal and -4 factors reduce to x²;
    # g and g(-x) coincide mod 2 and their total multiplicity q/2 is even.
    assert sp.Poly(g.as_expr()-g.as_expr().subs(x, -x), x, modulus=2).is_zero
    for k in range(4, 21):
        Q = 2**k
        assert int(cubic_trace.subs(q, Q)) % 2 == 1
        assert int(older_trace.subs(q, Q)) % 6 == 0
    print("scope: cubic completion fails graph triangle-trace parity")
    print("scope: rational-root completion passes this parity test only")


def verify_hoffman_divisibility_obstruction() -> None:
    """Annihilator evaluation rejects the older ledger as an integer matrix.

    If A is symmetric integral, A1=q1, and q is simple, any integral h
    annihilating its other eigenspaces has h(A)=h(q)J/n. Thus n divides
    h(q). Repeated factors in h do not affect the validity of this test.
    """
    x = sp.symbols("x")
    odd_factors = [
        x**2 + 2*x - 1, x**2 - 2*x - 1, x**2 - 1,
        x**2 - (2*q - 3), x**2 - q - 1, x**2 - q + 1,
    ]
    h = (x + 4) * (x**2 - q) * sp.prod(odd_factors)
    # Every other factor evaluates to an odd integer at even q.
    for factor in odd_factors:
        value = sp.Poly(factor.subs(x, q), q)
        assert int(value.TC()) % 2 == 1
    for k in range(4, 21):
        Q = 2**k
        value = int(h.subs({x: Q, q: Q}))
        valuation = (abs(value) & -abs(value)).bit_length() - 1
        assert valuation == k + 2 < 2*k
        assert value % (Q*Q) != 0

    # The defect spectrum independently fails the same regular-matrix test.
    defect_h = ((x-q+17)*(x-q+2)*(x+q-2)*(x+1)*(x+2)*x
                * ((x-q+4)**2-8))
    for k in range(4, 21):
        Q = 2**k
        # At q16 the q-17 and -1 roots coincide; keep only one copy.
        reduced = sp.Poly(defect_h.subs(q, Q), x).sqf_part()
        value = int(reduced.eval(Q-1))
        valuation = (abs(value) & -abs(value)).bit_length() - 1
        assert valuation == (4 if Q == 16 else k+4)
        assert valuation < 2*k

    # Positive calibration: the actual q4 graph must satisfy the identity,
    # even though its defect is disconnected and its adjacency is singular.
    control = runpy.run_path(str(Path(__file__).with_name(
        "binary_q4_fixed_free_disconnected_control.py")))
    A = sp.zeros(16)
    for u, v in control["A_EDGES"]:
        A[u, v] = A[v, u] = 1
    minimal = A.charpoly(x).as_poly().sqf_part()
    h4, remainder = sp.div(minimal, sp.Poly(x - 4, x))
    assert remainder.is_zero
    scale = int(h4.eval(4))
    assert scale % 16 == 0
    h4_A = sp.zeros(16)
    for coefficient in h4.all_coeffs():
        h4_A = h4_A*A + coefficient*sp.eye(16)
    assert h4_A == (scale // 16)*sp.ones(16)
    print("scope: older completion fails Hoffman divisibility: v2(h(q))=k+2<2k")
    print("scope: its defect spectrum also fails integer regular realization")
    print("verified: actual q4 graph satisfies the integer projector identity")


if __name__ == "__main__":
    verify_symbolically()
    verify_uniform_cubic_completion()
    verify_graph_parity_scope()
    verify_hoffman_divisibility_obstruction()
    for Q in (16, 32, 64, 128, 256):
        verify_at(Q)
    print("verified: both completions pass the stated defect-moment tests")
