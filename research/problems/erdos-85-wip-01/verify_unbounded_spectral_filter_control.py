#!/usr/bin/env python3
"""Exact polynomial identities and compressed spectral checks, not graphs.

Standard library only. No expansion of the degree-q^2 characteristic
polynomial and no graph-realizability claim.
"""

from fractions import Fraction as F
from math import comb, prod
from pathlib import Path
import runpy


def trim(p):
    p = list(p)
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p


def add(*polys):
    out = [0] * max(map(len, polys))
    for p in polys:
        for i, c in enumerate(p):
            out[i] += c
    return trim(out)


def scale(p, c):
    return trim([c * x for x in p])


def mul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i+j] += x*y
    return trim(out)


def power(p, n):
    out = [1]
    for _ in range(n):
        out = mul(out, p)
    return out


def evaluate(p, t):
    out = F(0)
    for c in reversed(p):
        out = out*t + c
    assert out.denominator == 1
    return int(out)


def configuration(alpha):
    q = [0, 0, alpha]
    numerators = [
        ([48, -8, 1], 16), ([-24, 1], 8),
        ([-544, -28, 46, 11, 5], 32),
        ([496, 38, -43, -6, 3], 16),
        ([-512, -36, 34, 1, 5], 32),
    ] if alpha == 1 else [
        ([12, -4, 1], 4), ([-12, 1], 4),
        ([-72, -6, 15, 5, 2], 8),
        ([60, 11, -14, -3, 6], 4),
        ([-64, -10, 9, 1, 2], 8),
    ]
    counts = [scale(p, F(1, denominator)) for p, denominator in numerators]
    squares = [[4], [8], [0, -alpha, alpha], q, [0, alpha, alpha]]
    real = [(q, [1]), ([-4], scale(q, F(1, 4))), ([-2], [2]), ([4], [1])]
    return q, counts, squares, real


def symbolic_moment(k, COUNTS, SQUARES, REAL):
    terms = [mul(count, power(root, k)) for root, count in REAL]
    if k % 2 == 0:
        terms += [scale(mul(count, power(a, k//2)), 2)
                  for a, count in zip(SQUARES, COUNTS)]
    return add(*terms)


def symbolic_checks(alpha):
    Q, COUNTS, SQUARES, REAL = configuration(alpha)
    targets = [power(Q, 2), [0], power(Q, 3),
               add(power(Q, 3), scale(Q, -16), [48]),
               mul(power(Q, 3), add(scale(Q, 2), [-1]))]
    for k, target in enumerate(targets):
        assert symbolic_moment(k, COUNTS, SQUARES, REAL) == target, k
    r = add(Q, [-1])
    for k, target in enumerate([power(Q, 2), [0], mul(power(Q, 2), r)]):
        terms = [power(r, k)]
        terms += [mul(count, power(add(r, scale(power(root, 2), -1)), k))
                  for root, count in REAL[1:]]
        terms += [scale(mul(count, power(add(r, scale(a, -1)), k)), 2)
                  for a, count in zip(SQUARES, COUNTS)]
        assert add(*terms) == target, k
    # Exact coefficients after t=32+u establish positivity for every u>=0.
    for p in COUNTS:
        shifted = [sum(p[i] * comb(i, k) * 32**(i-k)
                       for i in range(k, len(p))) for k in range(len(p))]
        assert shifted[0] > 0 and all(c >= 0 for c in shifted)
        # For t divisible by32, each nonconstant monomial and constant
        # separately takes an integer value.
        assert F(p[0]).denominator == 1
        assert all((F(c) * 32**i).denominator == 1 for i, c in enumerate(p))
    print(f"alpha={alpha}: symbolic A moments0..4, D moments0..2, uniform multiplicities PASS")


def v2(n):
    assert n > 0
    return (n & -n).bit_length() - 1


def main():
    base = Path(__file__).parent
    nb = runpy.run_path(str(base / "verify_nonbacktracking_positivity_audit.py"))
    for alpha in (1, 2):
        symbolic_checks(alpha)
        Q, COUNTS, SQUARES, REAL = configuration(alpha)
        for j in range(5, 13):
            t = 2**j
            q = alpha*t*t
            n = q*q
            pairs = {evaluate(a, t): evaluate(c, t) for a, c in zip(SQUARES, COUNTS)}
            real = {q: 1, -4: q//4, -2: 2, 4: 1}
            assert len(pairs) == 5 and min(pairs.values()) > 0
            assert sum(real.values()) + 2*sum(pairs.values()) == n
            assert max([x*x for x in real if x != q] + list(pairs)) <= 2*(q-1)
            assert min(pairs) > 0 and 0 not in real

            def moment(k):
                return sum(c*x**k for x, c in real.items()) + (
                    2*sum(c*a**(k//2) for a, c in pairs.items()) if k % 2 == 0 else 0)

            assert [moment(k) for k in range(5)] == [
                n, 0, n*q, q**3-16*q+48, q**3*(2*q-1)]
            assert 2*n <= moment(3) <= n*q
            # Factorwise proof of P_A=1 modulo4, not truncated moment testing.
            assert all(a % 4 == 0 for a in pairs)
            assert all(x % 4 == 0 or (x % 4 == 2 and c % 2 == 0)
                       for x, c in real.items())
            d = {q-1: 1}
            for x, c in real.items():
                if x != q:
                    mu = q-1-x*x
                    d[mu] = d.get(mu, 0) + c
            for a, c in pairs.items():
                mu = q-1-a
                d[mu] = d.get(mu, 0) + 2*c
            assert len(d) == 7 and sum(d.values()) == n
            assert sum(c*x for x, c in d.items()) == 0
            assert sum(c*x*x for x, c in d.items()) == n*(q-1)
            assert all(abs(x) < q-1 for x in d if x != q-1)
            assert all(x % 4 == 3 for x in d) and n % 2 == 0
            assert (n*(q-1)//2-n) % 2 == 0  # D Ihara prefactor is a square
            # Six distinct squared values exhaust the twelve residual A roots.
            squared_support = {16, 4, 8, q-alpha*t, q, q+alpha*t}
            assert len(squared_support) == 6
            h_a = prod(q*q-a for a in squared_support)
            h_d = prod(q-1-x for x in d if x != q-1)
            assert h_d == prod(squared_support) == 512*q*q*(q-alpha)
            assert v2(h_a) == v2(h_d) == 4*j+9+3*(alpha-1)
            assert h_a % (2*n) == h_d % (2*n) == 0
            assert (h_a//n-prod(squared_support)) % 2 == 0
            traces = nb["spectral_traces"](n, q, moment, 20)
            counts = [nb["primitive_count"](traces, k) for k in range(1, 21)]
            assert all(c >= 0 and c.denominator == 1 for c in counts)
            print(f"alpha={alpha}, j={j}, q={q}: compressed ledger, residue proofs, "
                  f"Hoffman v2={4*j+9+3*(alpha-1)}, cycle calibration PASS")
    print("No graph or integer-matrix realization has been constructed.")


if __name__ == "__main__":
    main()
