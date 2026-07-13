#!/usr/bin/env python3
"""
Certificate for cube-root-3-irrational-oq-04 S29: the 24th continued-fraction
convergent of ∛3 is a valid UPPER bound (cbrt3 < 247706213128/171749895599).

Independently re-derives the CF expansion of ∛3 to 160 digits, the 24th
convergent via the recursion, and the EXACT-INTEGER cube-direction check
p^3 vs 3 q^3 (the inequality `norm_num` discharges in the Lean theorem
`cbrt3_lt_two_four_seven_seven_zero_six_two_one_three_one_two_eight_over_...`).

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
    a = cf_expansion(c, 26)
    print("CF a[0..25] =", a[:26])
    assert a[:24] == [1, 2, 3, 1, 4, 1, 5, 1, 1, 6, 2, 5, 8, 3, 3, 4, 2, 6, 4, 4,
                      1, 3, 2, 3], "CF prefix mismatch"
    assert a[23] == 3, f"a23 expected 3, got {a[23]}"

    conv = convergents(a)
    a23, p23, q23 = conv[23]                    # 24th convergent (index 23)
    print(f"a23 = {a23}")
    print(f"24th convergent p23/q23 = {p23}/{q23}")
    assert (p23, q23) == (247706213128, 171749895599), "convergent mismatch"

    # exact recursion check from the 22nd/23rd convergents
    _, p21, q21 = conv[21]
    _, p22, q22 = conv[22]
    assert p23 == 3 * p22 + p21 and q23 == 3 * q22 + q21, "recursion mismatch"

    # exact-integer cube direction: p^3 > 3 q^3  <=>  (p/q)^3 > 3  <=>  cbrt3 < p/q
    lhs = p23 ** 3
    rhs = 3 * q23 ** 3
    print(f"p23^3       = {lhs}")
    print(f"3*q23^3     = {rhs}")
    print(f"diff p^3-3q^3 = {lhs - rhs}  (>0 => valid UPPER bound)")
    assert lhs > rhs, "NOT an upper bound!"

    relgap = abs(mp.mpf(p23) / q23 - c) / c
    print(f"relative gap = {mp.nstr(relgap, 6)}")
    print("PASS: cbrt3 < 247706213128/171749895599 (24th CF convergent, upper).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
