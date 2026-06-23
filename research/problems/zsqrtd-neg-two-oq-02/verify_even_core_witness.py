#!/usr/bin/env python3
"""
S9 certificate for zsqrtd-neg-two-oq-02 (Legendre three-square sufficiency).

Resolves the EVEN-CORE residual that S8 flagged as the last open sub-task of the
sufficiency wiring, and CORRECTS the S8 suggestion that an even-core thin-prime
witness might be "cleaner" than keeping a Dirichlet witness.

Background (knowledge.md S8):
  After wiring `ThreeSquaresSingleAP`, the ODD 4-free cores (n % 8 in {1,3,5})
  are discharged uniformly: a prime p == 1 (mod 4n) gives legendreSym(p,-n)=1,
  fed to (relaxed) dirichlet_key_lemma. The ONLY residual witness content is the
  EVEN 4-free cores n % 8 in {2,6} (4 // n) -- legendreSym_neg_n_eq_one requires
  Odd n (the Jacobi bottom must be odd), so it cannot serve them.

The odd residue-3 route (S3/S5) discharged its class via a THIN PRIME deficit:
  pick odd t with s := (m - t^2)/2 PRIME; s % 4 == 1 is then automatic, so
  s = a^2 + b^2 (Fermat, Nat.Prime.sq_add_sq), giving
      m = t^2 + (a+b)^2 + (a-b)^2.
The natural question (S8): does the same THIN-PRIME trick work for even cores
with EVEN t?  This script answers it.

Parity setup for n % 4 == 2:  a sum of three squares of n must use exactly two
ODD squares and one EVEN square (1+1+0 == 2 mod 4).  Writing the even one as t:
      n - t^2 = (odd)^2 + (odd)^2  ==  2 s,   s = (n - t^2)/2  (s odd),
and s = c^2 + d^2  <=>  n = t^2 + (c+d)^2 + (c-d)^2.   So an even-core witness is
exactly an even t with s := (n - t^2)/2 a SUM OF TWO SQUARES.

Two candidate statements, both with EVEN t and s = (n - t^2)/2:
  (STRICT)  s is a PRIME with s % 4 == 1            <- the residue-3-style trick
  (BROAD)   s is a SUM OF TWO SQUARES               <- the true characterization

FINDINGS (this script, n % 4 == 2, 2 < n <= NMAX):
  * STRICT fails on a SPORADIC set: {6,18,22,54,66,...} with members as large as
    68566 within 10^6 -- so the residue-3 thin-prime trick does NOT transplant to
    even cores. (For these n no even t makes (n-t^2)/2 a prime == 1 mod 4; e.g.
    n=22: t in {0,2,4} give s in {11, 9, 3}; 11,3 are primes == 3 mod 4 and 9 is
    composite -- yet 9 = 3^2+0^2 IS a sum of two squares, so 22 = 2^2+3^2+3^2.)
  * BROAD has ZERO failures, and the identity n = t^2+(c+d)^2+(c-d)^2 is exact.
    But "exists even t with (n-t^2)/2 a sum of two squares" is a REFORMULATION of
    "n is a sum of three squares with one even coordinate" -- it is the goal
    restated, NOT a reduction to an easier (Dirichlet-discharge-able) statement.

CONCLUSION (corrects S8): even cores have NO clean thin-prime reduction. They
must be discharged by the GENERAL QR/Minkowski route -- the relaxed
dirichlet_key_lemma with legendreSym p (-(n:int)) = 1 -- where the prime finder
is generalized to even n by splitting -n = -2m (m = n/2 odd) and choosing p's
residue class so legendreSym p (-2) * legendreSym p (-m)... resolves to +1.
The SingleAP lemma must therefore be extended for the factor of 2; it is not
replaced by a Fermat two-square shortcut. This saves a future Docker session
from attempting a (false) even-core thin-prime lemma.

Pure Python, no Docker, no Lean. Reproducible.
"""

from sympy import isprime

NMAX = 1_000_000


def is_excluded(n: int) -> bool:
    while n % 4 == 0:
        n //= 4
    return n % 8 == 7


def is_sum_two_squares(s: int) -> bool:
    """s >= 0 is a sum of two squares <=> every prime == 3 mod 4 divides s to
    an even power."""
    if s < 0:
        return False
    if s == 0:
        return True
    m = s
    d = 3
    while d * d <= m:
        if m % d == 0:
            e = 0
            while m % d == 0:
                m //= d
                e += 1
            if d % 4 == 3 and e % 2 == 1:
                return False
        d += 2
    if m % 4 == 3:  # leftover prime factor
        return False
    return True


def two_square_decomp(s: int):
    """Return (c,d), c>=d>=0, c^2+d^2 = s (assumes s is a sum of two squares)."""
    c = int(s ** 0.5)
    while c >= 0:
        r = s - c * c
        d = int(r ** 0.5)
        for dd in (d - 1, d, d + 1):
            if 0 <= dd <= c and c * c + dd * dd == s:
                return (c, dd)
        c -= 1
    return None


def main() -> None:
    strict_fail = []
    broad_fail = []
    identity_fail = []
    residue_bad = []
    excluded_bad = []
    max_t = 0
    count = 0

    n = 6
    while n <= NMAX:
        if n % 4 == 2:
            count += 1
            if n % 8 not in (2, 6):
                residue_bad.append(n)
            if is_excluded(n):
                excluded_bad.append(n)

            ok_strict = False
            broad_witness = None
            t = 0
            while t * t < n:
                rem = n - t * t
                if rem % 2 == 0:
                    s = rem // 2
                    if not ok_strict and s >= 2 and s % 4 == 1 and isprime(s):
                        ok_strict = True
                    if broad_witness is None and is_sum_two_squares(s):
                        broad_witness = (t, s)
                t += 2

            if not ok_strict:
                strict_fail.append(n)
            if broad_witness is None:
                broad_fail.append(n)
            else:
                t, s = broad_witness
                max_t = max(max_t, t)
                cd = two_square_decomp(s)
                if cd is None:
                    identity_fail.append((n, "no decomp", s))
                else:
                    c, d = cd
                    if t * t + (c + d) ** 2 + (c - d) ** 2 != n:
                        identity_fail.append((n, t, c, d))
        n += 4

    print("=" * 70)
    print(f"EVEN-CORE witness certificate  (n == 2 mod 4, 2 < n <= {NMAX})")
    print("=" * 70)
    print(f"cores checked (n % 4 == 2):              {count}")
    print(f"residue check (all n%8 in {{2,6}}):        "
          f"{'OK' if not residue_bad else residue_bad[:10]}")
    print(f"excluded among them (expect 0):          {len(excluded_bad)}")
    print()
    print(f"STRICT (prime, s%4==1) FAILURES:         {len(strict_fail)}  "
          f"(max {max(strict_fail) if strict_fail else None})")
    print(f"   sporadic set: {strict_fail}")
    print()
    print(f"BROAD (sum-of-two-squares) FAILURES:     {len(broad_fail)}  "
          f"{'OK' if not broad_fail else broad_fail[:20]}")
    print(f"identity n=t^2+(c+d)^2+(c-d)^2 FAILURES:  {len(identity_fail)}  "
          + (str(identity_fail[:5]) if identity_fail else "OK"))
    print(f"max even t needed (broad):               {max_t}")
    print("=" * 70)
    print("INTERPRETATION:")
    print(" * STRICT fails sporadically => the residue-3 thin-prime trick does")
    print("   NOT transplant to even cores.")
    print(" * BROAD always holds + identity exact, but it is a reformulation of")
    print("   the goal, not a Dirichlet-reducible statement.")
    print(" => even cores need the general QR/Minkowski (relaxed dirichlet_key_lemma)")
    print("    route with the prime finder extended to the factor of 2 in -n=-2m.")
    ok = (not broad_fail and not identity_fail
          and not residue_bad and not excluded_bad)
    print("=" * 70)
    print("RESULT:", "BROAD + identity + residue checks PASS"
          if ok else "*** CHECKS FAILED ***")


if __name__ == "__main__":
    main()
