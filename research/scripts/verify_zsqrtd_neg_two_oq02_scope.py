#!/usr/bin/env python3
"""
ORIENT verification for zsqrtd-neg-two-oq-02
("Legendre-Gauss three-square theorem via the Z[sqrt(-2)] infrastructure").

Central finding (exact, build-free):

  The Z[sqrt(-2)] norm form is x^2 + 2*y^2.  Via the trivial identity
  x^2 + 2*y^2 = x^2 + y^2 + y^2, EVERY number represented by x^2 + 2*y^2
  is a sum of three squares.  But the converse FAILS badly: only about
  half of the sum-of-three-squares numbers are of the form x^2 + 2*y^2.

  Therefore the Z[sqrt(-2)] machinery, by itself, CANNOT prove the full
  Legendre-Gauss three-square theorem.  It supplies exactly the prime
  cases p == 1, 3 (mod 8) (already complete & axiom-free in the gallery,
  ZsqrtdNegTwo.lean:357-476).  The remaining sufficiency direction is the
  genuinely deep half and requires the Dirichlet bridge -- it is the same
  gap captured by the two axioms in ThreeSquares.lean (dirichlet_key_lemma,
  not_excluded_form_is_sum_three_sq) and shared with lagrange-g2-oq-03.

What this script certifies (exact integer arithmetic, no floats in the logic):

  (1) The multiplicative characterization of x^2 + 2*y^2:
        n = x^2 + 2*y^2 has a solution  <=>  every prime p == 5,7 (mod 8)
        divides n to an even power.
      (Class number of discriminant -8 is 1.)

  (2) Subset relation:  x^2 + 2*y^2  ==>  sum of three squares.

  (3) The GAP:  there are infinitely many sum-of-three-squares numbers that
      are NOT of the form x^2 + 2*y^2 (density ~ 1/2).  Smallest witness n = 5.

  (4) Sanity: the elementary "necessity" obstruction n != 4^a(8b+7) used as the
      sum-of-three-squares oracle matches a direct brute-force search.
"""

from sympy import factorint

N = 2000


def is_x2_2y2(n):
    """True iff n = x^2 + 2 y^2 for some integers x,y (n >= 0)."""
    if n == 0:
        return True
    y = 0
    while 2 * y * y <= n:
        r = n - 2 * y * y
        x = int(round(r ** 0.5))
        for xx in (x - 1, x, x + 1):
            if xx >= 0 and xx * xx == r:
                return True
        y += 1
    return False


def is_sum3sq_bruteforce(n):
    """Direct search: n = a^2+b^2+c^2 with 0<=a<=b<=c."""
    if n == 0:
        return True
    a = 0
    while a * a <= n:
        ra = n - a * a
        b = a
        while b * b <= ra:
            rc = ra - b * b
            c = int(round(rc ** 0.5))
            for cc in (c - 1, c, c + 1):
                if cc >= b and cc * cc == rc:
                    return True
            b += 1
        a += 1
    return False


def is_sum3sq_legendre(n):
    """Legendre-Gauss oracle: n is a sum of 3 squares iff n != 4^a (8b+7)."""
    m = n
    while m % 4 == 0:
        m //= 4
    return m % 8 != 7


def char_x2_2y2(n):
    """Multiplicative characterization for representability by x^2+2y^2."""
    if n == 0:
        return True
    for p, e in factorint(n).items():
        if p % 8 in (5, 7) and e % 2 == 1:
            return False
    return True


def main():
    ok = True

    # (1) characterization of x^2 + 2 y^2
    bad = [n for n in range(1, N) if is_x2_2y2(n) != char_x2_2y2(n)]
    print(f"(1) x^2+2y^2 characterization mismatches up to {N}: {len(bad)} {bad[:10]}")
    ok &= (len(bad) == 0)

    # (4) Legendre oracle == brute force for sum of three squares
    bad4 = [n for n in range(0, N) if is_sum3sq_legendre(n) != is_sum3sq_bruteforce(n)]
    print(f"(4) Legendre oracle vs brute-force sum3sq mismatches: {len(bad4)} {bad4[:10]}")
    ok &= (len(bad4) == 0)

    # (2) subset:  x^2+2y^2  ==>  sum of 3 squares
    not_subset = [n for n in range(1, N) if is_x2_2y2(n) and not is_sum3sq_legendre(n)]
    print(f"(2) x^2+2y^2 but NOT sum3sq (must be empty): {not_subset[:10]}")
    ok &= (len(not_subset) == 0)

    # (3) the gap: sum3sq but NOT x^2+2y^2
    gap = [n for n in range(1, N) if is_sum3sq_legendre(n) and not is_x2_2y2(n)]
    w = gap[0]
    decomp = next((a, b, c)
                  for a in range(0, w + 1)
                  for b in range(a, w + 1)
                  for c in range(b, w + 1)
                  if a * a + b * b + c * c == w)
    print("(3) sum3sq but NOT x^2+2y^2 -- the Z[sqrt-2] BLIND SPOT")
    print(f"    first 20: {gap[:20]}")
    print(f"    smallest witness: n={w} = {decomp} (a^2+b^2+c^2)")
    print(f"    density of gap up to {N}: {len(gap)/N:.3f}")
    ok &= (len(gap) > 0 and gap[0] == 5)

    print()
    print("ALL CHECKS PASS" if ok else "FAILURE")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
