#!/usr/bin/env python3
"""
Build-free certificate for the CORRECTED per-residue sufficiency architecture of
Legendre's three-square theorem (proofs/Proofs/ThreeSquares.lean).

CONTEXT
-------
The registered flagship ThreeSquares.lean discharges the sufficiency direction
  ¬IsExcludedForm n  ⟹  ∃ x y z, x²+y²+z² = n
through a single key lemma `dirichlet_key_lemma` whose hypothesis is

    ∃ d > 0, p = d·n − 1 prime, legendreSym p (−d) = 1.

(The same isolated existence statement is `DirichletWitnessProperty` in the
unregistered reduction PR #24443.)

This certificate establishes two things over a large range of 4-free cores:

  [GAP]  The `legendreSym p (−d) = 1` witness is UNSATISFIABLE for every core
         m ≡ 3 (mod 8).  So the file's docstring plan ("n ≡ 3 mod 8: use d = 2")
         and the single-lemma architecture cannot cover the residue-3 class.
         (Corroborates audit PR #24529.)

  [FIX]  Each non-excluded 4-free core m (m ≢ 7 mod 8, 4 ∤ m) is a sum of three
         squares via a residue-split:
           • m ≡ 1,2,5,6 (mod 8): the Dirichlet/Minkowski witness EXISTS, so
             `dirichlet_key_lemma` applies.
           • m ≡ 3 (mod 8):  the TWO-SQUARE route works instead —
             ∃ odd t with t² ≤ m and mm = (m − t²)/2 a prime with mm % 4 ≠ 3,
             whence (Mathlib `Nat.Prime.sq_add_sq`) mm = a² + b² and
                 m = t² + (a + b)² + (a − b)².
             (Algebra: (a+b)²+(a−b)² = 2(a²+b²) = 2·mm = m − t².)

The general n is reduced to its 4-free core m by the already-proved
4-power-stripping lemmas (n = 4^a·m; if m = x²+y²+z² then n = (2^a x)²+…).

Pure standard library; no Lean build required.
"""

from math import isqrt


def core(n):
    """Return (a, m) with n = 4^a * m and 4 ∤ m."""
    a = 0
    while n % 4 == 0:
        n //= 4
        a += 1
    return a, n


def is_excluded(n):
    """n is of the excluded form 4^a(8b+7) iff its 4-free core is ≡ 7 mod 8."""
    return core(n)[1] % 8 == 7


def legendre(a, p):
    """Legendre symbol (a|p) for odd prime p, via Euler's criterion."""
    a %= p
    if a == 0:
        return 0
    r = pow(a, (p - 1) // 2, p)
    return r - p if r == p - 1 else r  # +1 or -1


def is_prime(n):
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    d = 3
    while d * d <= n:
        if n % d == 0:
            return False
        d += 2
    return True


def dirichlet_witness(m, dmax=4000):
    """∃ d>0 with p = d·m − 1 prime and legendreSym p (−d) = 1."""
    for d in range(1, dmax + 1):
        p = d * m - 1
        if p > 2 and is_prime(p) and legendre(-d, p) == 1:
            return (d, p)
    return None


def two_square_route(m):
    """For m ≡ 3 (mod 8), 4-free: find odd t, prime mm=(m−t²)/2 with mm%4≠3,
    and a,b with a²+b²=mm; verify m = t²+(a+b)²+(a−b)²."""
    if m == 3:
        return ('small', (1, 1, 1))  # 3 = 1²+1²+1²
    t = 1
    while t * t < m:
        if (m - t * t) % 2 == 0:
            mm = (m - t * t) // 2
            if mm >= 1 and mm % 4 != 3 and is_prime(mm):
                for a in range(isqrt(mm) + 1):
                    b2 = mm - a * a
                    b = isqrt(b2)
                    if b * b == b2:
                        x, y, z = t, a + b, a - b
                        if x * x + y * y + z * z == m:
                            return (t, (x, y, z))
        t += 2
    return None


def brute_three_sq(n):
    r = isqrt(n)
    for x in range(r + 1):
        for y in range(x, isqrt(n - x * x) + 1):
            z2 = n - x * x - y * y
            if z2 >= 0 and isqrt(z2) ** 2 == z2:
                return (x, y, isqrt(z2))
    return None


def main():
    PER_CLASS = 750
    # ---- [GAP] witness unsatisfiable for m ≡ 3 mod 8 -------------------------
    gap_checked = 0
    gap_violations = []
    m = 3
    while gap_checked < PER_CLASS:
        if m % 4 != 0 and m % 8 == 3:
            if dirichlet_witness(m) is not None:
                gap_violations.append(m)
            gap_checked += 1
        m += 1
    print(f"[GAP] cores m≡3 mod8 checked: {gap_checked}; "
          f"witness-FOUND (should be 0): {len(gap_violations)} {gap_violations[:10]}")

    # ---- [FIX] every non-excluded 4-free core is covered --------------------
    stats = {r: [0, []] for r in (1, 2, 3, 5, 6)}
    m = 1
    while min(v[0] for v in stats.values()) < PER_CLASS:
        if m % 4 != 0 and m % 8 != 7:
            r = m % 8
            if r in stats and stats[r][0] < PER_CLASS:
                if r == 3:
                    ok = two_square_route(m) is not None
                else:
                    ok = dirichlet_witness(m) is not None
                # cross-check the route's conclusion against brute force
                ok = ok and (brute_three_sq(m) is not None)
                stats[r][0] += 1
                if not ok:
                    stats[r][1].append(m)
        m += 1
    all_ok = True
    for r, (tot, miss) in sorted(stats.items()):
        status = "OK" if not miss else f"FAIL {miss[:10]}"
        if miss:
            all_ok = False
        route = "two-square" if r == 3 else "dirichlet-witness"
        print(f"[FIX] core m≡{r} mod8 ({route}): {tot} cores, {status}")

    # ---- [SANITY] excluded ⟺ not a sum of three squares ---------------------
    excl_bad = []
    for n in range(1, 4000):
        if is_excluded(n) and brute_three_sq(n) is not None:
            excl_bad.append(n)
        if (not is_excluded(n)) and brute_three_sq(n) is None:
            excl_bad.append(-n)
    print(f"[SANITY] excluded ⟺ ¬3-sq mismatches in [1,4000): {len(excl_bad)} {excl_bad[:10]}")

    ok = (not gap_violations) and all_ok and (not excl_bad)
    print("\nRESULT:", "PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
