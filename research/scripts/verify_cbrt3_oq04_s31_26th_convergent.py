#!/usr/bin/env python3
"""
Certificate for cube-root-3-irrational-oq-04 S31: the 26th continued-fraction
convergent of ∛3 is a valid UPPER bound (cbrt3 < 1310497171657/908647988973).

Independently re-derives the CF expansion of ∛3 to 160 digits, the 26th
convergent via the recursion, and the EXACT-INTEGER cube-direction check
p^3 vs 3 q^3 (the inequality `norm_num` discharges in the Lean theorem
`cbrt3_lt_one_three_one_zero_four_nine_seven_one_seven_one_six_five_seven_over_...`).

The 26th convergent has odd index (25), so it lies on the UPPER side of ∛3
(alternating with the lower-side 25th convergent 1062790958529/736898093374).

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
    a = cf_expansion(c, 28)
    print("CF a[0..27] =", a[:28])
    assert a[:26] == [1, 2, 3, 1, 4, 1, 5, 1, 1, 6, 2, 5, 8, 3, 3, 4, 2, 6, 4, 4,
                      1, 3, 2, 3, 4, 1], "CF prefix mismatch"
    assert a[25] == 1, f"a25 expected 1, got {a[25]}"

    conv = convergents(a)
    a25, p25, q25 = conv[25]                    # 26th convergent (index 25)
    print(f"a25 = {a25}")
    print(f"26th convergent p25/q25 = {p25}/{q25}")
    assert (p25, q25) == (1310497171657, 908647988973), "convergent mismatch"

    # exact recursion check from the 24th/25th convergents
    _, p23, q23 = conv[23]
    _, p24, q24 = conv[24]
    assert p25 == 1 * p24 + p23 and q25 == 1 * q24 + q23, "recursion mismatch"

    # exact-integer cube direction: p^3 > 3 q^3  <=>  (p/q)^3 > 3  <=>  cbrt3 < p/q
    lhs = p25 ** 3
    rhs = 3 * q25 ** 3
    print(f"p25^3       = {lhs}")
    print(f"3*q25^3     = {rhs}")
    print(f"diff p^3-3q^3 = {lhs - rhs}  (>0 => valid UPPER bound)")
    assert lhs > rhs, "NOT an upper bound!"

    relgap = abs(mp.mpf(p25) / q25 - c) / c
    print(f"relative gap = {mp.nstr(relgap, 6)}")
    print("PASS: cbrt3 < 1310497171657/908647988973 (26th CF convergent, upper).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
