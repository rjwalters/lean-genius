#!/usr/bin/env python3
"""
Reproducible verification of the Waring g(k) lower-bound witnesses behind

    lagrange-four-squares-waring-g2-oq-01

This slug ships, for each k, a Lean theorem of the shape

    ¬ IsSumOfKthPowers (g(k) - 1) N_k          (the "miss by 1" lower bound)

establishing g(k) ≥ <known value>, via the counting+omega template
(bound f_i ≤ 2 → lift to Fin 3 → fiber-count → omega). The same witness
arithmetic underpins all five shipped lower-bound files
(Counting, CountingG4..G7 for k = 3..7), the paste-port-ready S8 (k = 8),
and the k = 9 look-ahead.

Until now those numbers were only verified inside session transcripts
(ephemeral). This script makes them reproducible: it re-derives every
constant from the Mahler formula and checks, by the exact counting argument
the Lean proof uses, that N_k is infeasible with g(k)-1 summands but feasible
with g(k). Run:

    python3 verify_witnesses.py

Exits 0 with "ALL CHECKS PASSED" iff every assertion holds.
Pure standard library (no dependencies).

Definitions
-----------
  q_k  = floor((3/2)^k)
  N_k  = q_k * 2^k - 1            (the hardest number < 3^k to represent)
  g(k) = 2^k + q_k - 2           (Mahler value; = known g(k) for k here)
  s_k  = g(k) - 1                 (the term count the Lean theorem refutes)

Soundness of "f_i ≤ 2": since N_k < 3^k, every k-th power summand is one of
0^k, 1^k, 2^k. So a representation of N_k by s summands is exactly a triple
(n0, n1, n2) of fiber sizes with

  n0 + n1 + n2 = s        and        n1 + 2^k * n2 = N_k.

The lower bound is the claim that this system is INFEASIBLE for s = s_k and
FEASIBLE (tight) for s = g(k).
"""

from fractions import Fraction

# Known values of g(k) (Niven 1936; Dickson/Pillai/Chen/etc.), for cross-check.
KNOWN_G = {3: 9, 4: 19, 5: 37, 6: 73, 7: 143, 8: 279, 9: 548}


def floor_three_halves_pow(k: int) -> int:
    """Exact floor((3/2)^k) via integer arithmetic (3^k // 2^k)."""
    return (3 ** k) // (2 ** k)


def counting_feasible(s: int, k: int, N: int) -> bool:
    """
    True iff N is a sum of s k-th powers using bases in {0,1,2}, i.e. there
    exist n0,n1,n2 >= 0 with n0+n1+n2 = s and n1 + 2^k*n2 = N.
    This mirrors exactly the Lean `IsSumOfKthPowers s N` reduction (since
    N < 3^k forces bases <= 2). Finite scan over n2.
    """
    twok = 2 ** k
    for n2 in range(0, N // twok + 1):
        rem = N - twok * n2          # must be covered by n1 ones
        n1 = rem                     # one base-1 summand per unit
        n0 = s - n1 - n2
        if n1 >= 0 and n0 >= 0:
            return True
    return False


def check(name, cond):
    print(f"  [{'ok  ' if cond else 'FAIL'}] {name}")
    assert cond, f"CHECK FAILED: {name}"


def main():
    for k in range(3, 10):
        q = floor_three_halves_pow(k)
        N = q * (2 ** k) - 1
        g = (2 ** k) + q - 2
        s = g - 1
        print(f"== k = {k}:  q={q}  N={N}  g(k)={g}  s=g-1={s} ==")

        # q_k is the floor, and STRICTLY below (3/2)^k (S6b audit: (3/2)^k is
        # never an integer for k >= 1, so q < (3/2)^k strictly, which is what
        # guarantees N_k = q·2^k + (2^k - 1) < 3^k).
        check(f"q < (3/2)^{k} strictly", q < Fraction(3, 2) ** k)
        check(f"q is the floor: q <= (3/2)^{k} < q+1",
              q <= Fraction(3, 2) ** k < q + 1)

        # Cross-check the Mahler value against the literature value.
        if k in KNOWN_G:
            check(f"g({k}) = {KNOWN_G[k]} (known)", g == KNOWN_G[k])

        # Soundness of the f_i <= 2 reduction: N < 3^k.
        check(f"N < 3^{k} (forces bases <= 2)", N < 3 ** k)

        # The decisive pair: infeasible at s = g-1, feasible (tight) at s = g.
        check(f"N NOT a sum of {s} = g-1 k-th powers (lower bound)",
              not counting_feasible(s, k, N))
        check(f"N IS a sum of {g} = g k-th powers (tightness)",
              counting_feasible(g, k, N))

        # Witness shape recorded in the session ledger: the optimal
        # representation uses (q-1) twos and (2^k - 1) ones.
        twos, ones = q - 1, (2 ** k) - 1
        check(f"witness (q-1)·2^{k} + (2^{k}-1)·1 = N",
              twos * (2 ** k) + ones * 1 == N)
        check(f"witness term count (q-1)+(2^{k}-1) = g({k})",
              twos + ones == g)

    print("\nALL CHECKS PASSED")


if __name__ == "__main__":
    main()
