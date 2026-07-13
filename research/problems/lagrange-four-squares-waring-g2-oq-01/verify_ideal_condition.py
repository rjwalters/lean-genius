#!/usr/bin/env python3
"""
Exact-integer verification of the *upper-bound* side of Waring's problem for

    lagrange-four-squares-waring-g2-oq-01

Companion to `verify_witnesses.py` / `verify_general_lower.py`, which certify
the **lower** bound g(k) >= 2^k + floor((3/2)^k) - 2 (the unconditional,
elementary half, formalised parametrically in PR #24228). Those artifacts say
nothing about the matching **upper** bound. This script fills that gap.

Background
----------
The full "ideal Waring" value is

    g(k) = 2^k + floor((3/2)^k) - 2

PROVIDED a number-theoretic side condition holds. The lower bound (this value
is necessary) is elementary. The upper bound (this value SUFFICES) is the deep
Dickson-Pillai-Rubugunday-Niven theorem (1936-1944): it is conditional on the
exactly-checkable

    Dickson-Pillai condition  (*):   r + q <= 2^k

where  q = floor((3/2)^k)  and  r = 3^k mod 2^k = 3^k - q * 2^k  (so that
{(3/2)^k} = r / 2^k). Condition (*) is *necessary and sufficient* for the
ideal value g(k) = 2^k + q - 2. When (*) fails, g(k) picks up an extra
floor((4/3)^k) term.

Mahler (1957) proved the strictly stronger sufficient condition

    Mahler condition  (M):   {(3/2)^k} <= 1 - (3/4)^k
                       <=>   r * 2^k <= 4^k - 3^k        (exact-integer form)

holds for all but finitely many k; Kubina-Wunderlich (1990) verified (*) for
all k <= 4.716e8. NO k is known where (*) fails, so the formula is believed to
hold for every k -- but this is open, contingent on an irrationality-measure
improvement for (3/2). (M) => (*), so verifying (M) also verifies (*).

What is elementary vs deep (HONEST boundary)
--------------------------------------------
  * Lower bound  g(k) >= 2^k + q - 2          : ELEMENTARY (counting argument,
                                                 formalised in #24228).
  * Checking (*) / (M) for a given k          : ELEMENTARY (this script; pure
                                                 big-integer arithmetic).
  * Implication  (*) ==> upper bound          : DEEP THEOREM (Dickson-Pillai-
                                                 Niven), NOT formalised, Mathlib
                                                 gap. This script does NOT prove
                                                 it -- it verifies the hypothesis.

So this certificate establishes: "for every k in the checked range the
hypothesis of the ideal-Waring theorem holds, hence g(k) = 2^k + floor((3/2)^k)
- 2 exactly, *modulo* the unformalised Dickson-Pillai-Niven implication."

Run:
    python3 verify_ideal_condition.py
Exits 0 with "ALL CHECKS PASSED" iff every assertion holds. Pure stdlib.
"""

# OEIS A002804 -- Waring's problem g(k), the literature values.
OEIS_A002804 = {
    1: 1, 2: 4, 3: 9, 4: 19, 5: 37, 6: 73, 7: 143, 8: 279,
    9: 548, 10: 1079, 11: 2132, 12: 4223,
}

K_MAX = 200  # exact big-integer arithmetic stays fast well beyond this


def data(k):
    """Return (M, q, r) with M=2^k, q=floor((3/2)^k), r=3^k mod 2^k."""
    M = 2 ** k
    P = 3 ** k
    q = P // M          # floor((3/2)^k)
    r = P - q * M       # 3^k mod 2^k  (= 2^k * frac((3/2)^k))
    return M, q, r


def main():
    failures = []
    mahler_fails = []

    for k in range(1, K_MAX + 1):
        M, q, r = data(k)

        # sanity: 0 <= r < M, and q*M + r == 3^k
        if not (0 <= r < M and q * M + r == 3 ** k):
            failures.append((k, "decomposition 3^k = q*2^k + r failed"))
            continue

        formula = M + q - 2  # conjectural ideal value 2^k + floor((3/2)^k) - 2

        # (*) Dickson-Pillai necessary&sufficient condition for g(k)=formula.
        ideal_star = (r + q <= M)

        # (M) Mahler's stronger sufficient condition, exact-integer form:
        #     {(3/2)^k} <= 1 - (3/4)^k  <=>  r * 2^k <= 4^k - 3^k.
        mahler = (r * M <= 4 ** k - 3 ** k)

        # (M) => (*): the Mahler condition must imply Dickson-Pillai.
        if mahler and not ideal_star:
            failures.append((k, "Mahler (M) held but Dickson-Pillai (*) failed"))

        # No exceptional k is known: (*) must hold throughout the checked range.
        if not ideal_star:
            failures.append((k, f"Dickson-Pillai (*) FAILS: r+q={r+q} > 2^k={M}"))

        if not mahler:
            mahler_fails.append(k)

        # Cross-check the formula against the literature where known.
        if k in OEIS_A002804 and formula != OEIS_A002804[k]:
            failures.append(
                (k, f"formula {formula} != OEIS A002804 {OEIS_A002804[k]}")
            )

    # Report a small table for the documented range.
    print("Waring ideal-condition verification (exact integer arithmetic)")
    print(f"  q = floor((3/2)^k),  r = 3^k mod 2^k,  formula = 2^k + q - 2")
    print()
    print(f"  {'k':>3} {'2^k':>8} {'q':>6} {'r':>8} {'r+q<=2^k':>9}"
          f" {'Mahler':>7} {'formula':>9} {'g(k)':>6}")
    for k in range(1, 13):
        M, q, r = data(k)
        formula = M + q - 2
        star = "yes" if r + q <= M else "NO"
        mah = "yes" if r * M <= 4 ** k - 3 ** k else "no"
        g = OEIS_A002804.get(k, "-")
        print(f"  {k:>3} {M:>8} {q:>6} {r:>8} {star:>9} {mah:>7}"
              f" {formula:>9} {str(g):>6}")
    print()
    print(f"  Dickson-Pillai (*) holds for ALL k = 1..{K_MAX}")
    print(f"  Mahler (M) fails only at k in {mahler_fails or 'none'}"
          f"  (small-k edges; (M) holds for every larger k in range)")
    print(f"  formula matched OEIS A002804 for k = 1..12")
    print()

    if failures:
        print("FAILURES:")
        for k, msg in failures:
            print(f"  k={k}: {msg}")
        raise SystemExit(1)

    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
