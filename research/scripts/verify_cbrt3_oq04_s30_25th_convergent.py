#!/usr/bin/env python3
"""
Certificate for cube-root-3-irrational-oq-04 S30: the 25th continued-fraction
convergent of ∛3 is a valid LOWER bound (1062790958529/736898093374 < cbrt3).

Independently re-derives the CF expansion of ∛3 to 160 digits, the 25th
convergent via the recursion, and the EXACT-INTEGER cube-direction check
p^3 vs 3 q^3 (the inequality `norm_num` discharges in the Lean theorem
`one_zero_six_two_seven_nine_zero_nine_five_eight_five_two_nine_over_...`).

The 25th convergent has even index (24), so it lies on the LOWER side of ∛3
(alternating with the upper-side 24th convergent 247706213128/171749895599).

Anti-typo discipline (a8/a14 history): the partial quotients are recomputed from
scratch, never re-quoted from a prior sketch tail.

Docker-independent. Requires mpmath.
"""
import mpmath as mp

mp.mp.dps = 160


def cf_expansion(x, n):
    a = []
    for _ in range(n):
        ai = int(mp.floor(x))
        a.append(ai)
        frac = x - ai
        if frac == 0:
            break
        x = 1 / frac
    return a


def convergents(a):
    pm1, pm2 = 1, 0
    qm1, qm2 = 0, 1
    out = []
    for ak in a:
        p = ak * pm1 + pm2
        q = ak * qm1 + qm2
        out.append((ak, p, q))
        pm2, pm1 = pm1, p
        qm2, qm1 = qm1, q
    return out


def main():
    c = mp.cbrt(3)
    a = cf_expansion(c, 27)
    print("CF a[0..26] =", a[:27])
    assert a[:25] == [1, 2, 3, 1, 4, 1, 5, 1, 1, 6, 2, 5, 8, 3, 3, 4, 2, 6, 4, 4,
                      1, 3, 2, 3, 4], "CF prefix mismatch"
    assert a[24] == 4, f"a24 expected 4, got {a[24]}"

    conv = convergents(a)
    a24, p24, q24 = conv[24]                    # 25th convergent (index 24)
    print(f"a24 = {a24}")
    print(f"25th convergent p24/q24 = {p24}/{q24}")
    assert (p24, q24) == (1062790958529, 736898093374), "convergent mismatch"

    # exact recursion check from the 23rd/24th convergents
    _, p22, q22 = conv[22]
    _, p23, q23 = conv[23]
    assert p24 == 4 * p23 + p22 and q24 == 4 * q23 + q22, "recursion mismatch"

    # exact-integer cube direction: p^3 < 3 q^3  <=>  (p/q)^3 < 3  <=>  p/q < cbrt3
    lhs = p24 ** 3
    rhs = 3 * q24 ** 3
    print(f"p24^3       = {lhs}")
    print(f"3*q24^3     = {rhs}")
    print(f"diff 3q^3-p^3 = {rhs - lhs}  (>0 => valid LOWER bound)")
    assert lhs < rhs, "NOT a lower bound!"

    relgap = abs(mp.mpf(p24) / q24 - c) / c
    print(f"relative gap = {mp.nstr(relgap, 6)}")
    print("PASS: 1062790958529/736898093374 < cbrt3 (25th CF convergent, lower).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
