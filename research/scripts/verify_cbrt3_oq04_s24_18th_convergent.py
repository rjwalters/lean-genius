#!/usr/bin/env python3
"""Certificate for cube-root-3-irrational-oq-04 S24.

Verifies the eighteenth simple-continued-fraction convergent of cbrt3 and the
exact integer cubing inequality behind the new helper theorem

    cbrt3 < 383473988 / 265886013   (UPPER bound).

Run: python3 research/scripts/verify_cbrt3_oq04_s24_18th_convergent.py
"""
from decimal import Decimal, getcontext


def cf_and_convergents(n_terms: int):
    getcontext().prec = 400
    g, three = Decimal(1.5), Decimal(3)
    for _ in range(800):  # high-iteration Newton for cbrt(3) at 400 digits
        g = (2 * g + three / (g * g)) / 3
    a, v = [], g
    for _ in range(n_terms):
        fl = int(v)
        a.append(fl)
        v = 1 / (v - fl)
    conv, pm2, pm1, qm2, qm1 = [], 1, a[0], 0, 1
    for k in range(1, len(a)):
        pk, qk = a[k] * pm1 + pm2, a[k] * qm1 + qm2
        conv.append((pk, qk))
        pm2, pm1, qm2, qm1 = pm1, pk, qm1, qk
    return a, conv


def main() -> None:
    a, conv = cf_and_convergents(20)
    expected_prefix = [1, 2, 3, 1, 4, 1, 5, 1, 1, 6, 2, 5, 8, 3, 3, 4, 2, 6, 4, 4]
    assert a == expected_prefix, f"CF prefix mismatch: {a}"

    # eighteenth convergent = p17/q17 (conv[] omits the 0th, so index 16), uses a17 = 6
    p, q = conv[16]
    assert a[17] == 6, a[17]
    assert (p, q) == (383473988, 265886013), (p, q)
    assert p == 6 * 59472423 + 26639450  # recurrence on 17th & 16th convergents
    assert q == 6 * 41235875 + 18470763

    lhs, rhs = p ** 3, 3 * q ** 3
    assert lhs == 56390731723337477324766272, lhs
    assert rhs == 56390731723337476944612591, rhs
    assert lhs > rhs, "expected an UPPER bound (p^3 > 3 q^3)"
    print("PASS: cbrt3 < 383473988/265886013 (18th convergent, a17=6)")
    print(f"  p^3 - 3 q^3 = +{lhs - rhs}  (rel gap {(lhs - rhs) / rhs:.3e})")


if __name__ == "__main__":
    main()
