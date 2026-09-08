#!/usr/bin/env python3
"""Reject a formal q16 ledger by Hoffman diagonal parity; standard library."""

from math import prod
from pathlib import Path
import runpy


ROOTS = [16, -4, -4, -4, -4, -2, -2, 4]
PAIRS = {2: 3, 14: 99, 22: 22}
DEFECT = {15: 1, -1: 5, 11: 2, 13: 6, 1: 198, -7: 44}


def moment(k):
    return sum(x**k for x in ROOTS) + (
        2 * sum(count * a**(k // 2) for a, count in PAIRS.items())
        if k % 2 == 0 else 0)


def v2(n):
    assert n != 0
    n = abs(n)
    return (n & -n).bit_length() - 1


def main():
    base = Path(__file__).parent
    integral = runpy.run_path(str(base / "verify_nonbacktracking_integrality_mod4.py"))
    nb = runpy.run_path(str(base / "verify_nonbacktracking_positivity_audit.py"))
    multiply = integral["multiply"]
    assert moment(0) == 256
    assert [moment(k) for k in range(1, 5)] == [0, 4096, 3888, 126976]
    assert 2 * 256 <= moment(3) <= 256 * 16
    assert all(x*x <= 30 for x in ROOTS if x != 16)
    assert max(PAIRS) <= 30
    assert all(x != 0 for x in ROOTS) and min(PAIRS) > 0
    p = [1]
    for x in ROOTS:
        p = multiply(p, [1, -x])
    for a, count in PAIRS.items():
        for _ in range(count):
            p = multiply(p, [1, 0, -a])
    assert len(p) == 257
    assert [x % 4 for x in p] == [1] + [0] * 256
    assert integral["mod4_square"](p)
    assert integral["moments_from_poly"](p, 256, 20) == [moment(k) for k in range(21)]

    induced = {15: 1}
    for x in ROOTS[1:]:
        mu = 15 - x*x
        induced[mu] = induced.get(mu, 0) + 1
    for a, count in PAIRS.items():
        mu = 15 - a
        induced[mu] = induced.get(mu, 0) + 2 * count
    assert induced == DEFECT
    assert sum(DEFECT.values()) == 256
    assert [sum(count * mu**k for mu, count in DEFECT.items())
            for k in range(1, 4)] == [0, 3840, 4320]
    assert all(abs(mu) < 15 for mu in DEFECT if mu != 15)
    pd = [1]
    for mu, count in DEFECT.items():
        for _ in range(count):
            pd = multiply(pd, [1, -mu])
    assert integral["mod4_square"](pd)
    target = [1] + [0] * 127 + [2] + [0] * 127 + [1]
    assert [x % 4 for x in pd] == target

    h_a = prod(16 - x for x in set(ROOTS[1:])) * prod(256 - a for a in PAIRS)
    h_d = prod(15 - mu for mu in DEFECT if mu != 15)
    assert h_a % 256 == h_d % 256 == 0
    assert (v2(h_a), v2(h_d)) == (8, 9)
    ha_poly = [1]
    for root in sorted(set(ROOTS[1:])):
        ha_poly = multiply(ha_poly, [-root, 1])
    for a in PAIRS:
        ha_poly = multiply(ha_poly, [-a, 0, 1])
    assert ha_poly[0] == 19712
    assert sum(c * 16**i for i, c in enumerate(ha_poly)) == h_a == 62136771840
    assert [c % 2 for c in ha_poly] == [0] * 9 + [1]
    assert h_a // 256 == 242721765
    assert (h_a // 256 - ha_poly[0]) % 2 == 1
    traces = nb["spectral_traces"](256, 16, moment, 20)
    counts = [nb["primitive_count"](traces, k) for k in range(1, 21)]
    assert all(c >= 0 and c.denominator == 1 for c in counts)
    assert all(c > 0 for c in counts[4:])
    print("A: degree 256 polynomial, low moments/window, P=1 mod4 PASS")
    print("D: induced ledger, traces, strict residual window, mod4 square PASS")
    print(f"Minimal Hoffman divisibility: v2(A)={v2(h_a)}, v2(D)={v2(h_d)} PASS")
    print("A primitive counts lengths3..8:", [int(c) for c in counts[2:8]])
    print("All-length A positivity/integrality follows from the companion proofs.")
    print("REJECTED: Hoffman scalar is odd but h(0) is even.")

    matrix_checks(base, integral, nb)


def matrix_checks(base, integral, nb):
    def matmul(a, b):
        return [[sum(x*y for x, y in zip(row, col)) for col in zip(*b)] for row in a]

    control = runpy.run_path(str(base / "binary_q4_fixed_free_disconnected_control.py"))
    rows = control["adjacency"](control["A_EDGES"])
    for name, adjacency, q in [("q4", rows, 4), ("triangle", [{1, 2}, {0, 2}, {0, 1}], 2)]:
        n = len(adjacency)
        a = [[int(j in adjacency[i]) for j in range(n)] for i in range(n)]
        assert all(a[i][i] == 0 and sum(a[i]) == q for i in range(n))
        assert all(a[i][j] == a[j][i] for i in range(n) for j in range(n))
        moments = nb["adjacency_moments"](adjacency, n)
        p = integral["poly_from_moments"](moments, n)
        quotient = [p[0]]
        for c in p[1:-1]:
            quotient.append(c + q * quotient[-1])
        assert p[-1] + q * quotient[-1] == 0
        # Horner evaluation of the nonprincipal characteristic factor.
        h = [[0] * n for _ in range(n)]
        for c in quotient:
            h = matmul(h, a)
            for i in range(n):
                h[i][i] += c
        scalar = 0
        for c in quotient:
            scalar = scalar*q + c
        assert scalar % n == 0 and scalar != 0
        scalar //= n
        assert all(value == scalar for row in h for value in row)
        assert (scalar - quotient[-1]) % 2 == 0
        power = [[int(i == j) for j in range(n)] for i in range(n)]
        for _ in range(8):
            power = matmul(power, a)
            assert all(power[i][i] % 2 == 0 for i in range(n))
        print(f"{name}: matrix Hoffman identity, parity correction, powers1..8 PASS")
    # The minimal triangle annihilator x+1 has odd constant and scalar 1.
    assert (2 + 1) // 3 == 1


if __name__ == "__main__":
    main()
