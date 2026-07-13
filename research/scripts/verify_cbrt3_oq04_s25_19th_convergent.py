"""S25 certificate: nineteenth CF convergent (index 18) lower bound for cbrt3.

Re-derives the simple continued fraction of 3^(1/3) to high precision (NOT
re-quoting any prior sketch tail, per this slug's a8/a14 typo history), recomputes
the convergent recursion, and confirms the cube-side direction so the new helper
`1593368375/1104779927 < cbrt3` lands on the correct (LOWER) side.

Run: python3 verify_cbrt3_oq04_s25_19th_convergent.py
"""

from decimal import Decimal, getcontext

getcontext().prec = 300


def cbrt3_highprec() -> Decimal:
    x = Decimal(3)
    g = Decimal("1.4422495703074083823216383107801")
    for _ in range(200):
        g = (2 * g + x / (g * g)) / 3
    return g


def cf(val: Decimal, n: int):
    a = []
    v = val
    for _ in range(n):
        ai = int(v)
        a.append(ai)
        v = 1 / (v - ai)
    return a


def main() -> None:
    c = cbrt3_highprec()
    assert abs(c ** 3 - 3) < Decimal(10) ** -290, "cbrt3 not converged"

    a = cf(c, 22)
    # Independent re-derivation of the prefix; must match OEIS A002945.
    expected = [1, 2, 3, 1, 4, 1, 5, 1, 1, 6, 2, 5, 8, 3, 3, 4, 2, 6, 4]
    assert a[: len(expected)] == expected, f"CF mismatch: {a[:len(expected)]}"

    # convergent recursion
    p_prev, p = 1, a[0]
    q_prev, q = 0, 1
    convs = [(p, q)]
    for i in range(1, len(a)):
        p, p_prev = a[i] * p + p_prev, p
        q, q_prev = a[i] * q + q_prev, q
        convs.append((p, q))

    # index 18 == nineteenth convergent, a18 = 4
    assert a[18] == 4, f"a18 expected 4, got {a[18]}"
    p18, q18 = convs[18]
    assert (p18, q18) == (1593368375, 1104779927), (p18, q18)

    cube = p18 ** 3
    three_q = 3 * q18 ** 3
    diff = cube - three_q
    side = "LOWER (< cbrt3)" if diff < 0 else "UPPER (> cbrt3)"
    print(f"a18 = {a[18]}")
    print(f"p18/q18 = {p18}/{q18}")
    print(f"p18^3   = {cube}")
    print(f"3*q18^3 = {three_q}")
    print(f"diff = {diff}  => {side}")
    assert diff < 0, "nineteenth convergent must be a LOWER bound"
    print("PASS: 1593368375/1104779927 < cbrt3 (nineteenth convergent, a18=4)")


if __name__ == "__main__":
    main()
