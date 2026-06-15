#!/usr/bin/env python3
"""
Erdős Problem #653 — FORMALIZATION DISCREPANCY check (build-free, exact arithmetic).

This script documents a *correctness* finding about the gallery entry, not a new
bound. It demonstrates that the quantity `g(n)` formalized in
`proofs/Proofs/Erdos653Problem.lean` is NOT the function studied in Erdős #653.

------------------------------------------------------------------------------
THE ACTUAL Erdős Problem #653 (erdosproblems.com/653)
------------------------------------------------------------------------------
Let x_1,...,x_n be n points in the plane with NO FOUR ON A CIRCLE (no four
concyclic). There must exist some x_i that has at least f(n) distinct distances
to the other points. Estimate f(n). Conjecture: f(n) >= (1 - o(1)) n.

So the studied function is a MIN–MAX with a forbidden-configuration hypothesis:

    f(n) = min over n-point sets S (no four concyclic) of  max_{p in S} R(p),

where R(p) = #distinct distances from p to the other points. Known bounds:
    f(n) > (3/8) n   (Erdős–Fishburn)
    f(n) > (7/10) n  (Csizmadia, current best)
    f(n) < n - c n^{2/3}.

------------------------------------------------------------------------------
WHAT THE GALLERY FILE FORMALIZES (a DIFFERENT quantity)
------------------------------------------------------------------------------
`Erdos653Problem.lean` defines, with NO concyclic hypothesis,

    g(n) = max over all n-point sets S of  numDistinctRValues(S)
         = max over S of  #{ R(p) : p in S }   (count of DISTINCT R-values).

This is neither a min–max nor does it forbid four concyclic points. It is the
DIVERSITY of the multiset {R(p)}, a different object. The file then states the
literature bounds (csizmadia_bound, upper_bound) as axioms ABOUT THIS g — i.e.
they are mis-attributed: those theorems are about f(n), not about this g(n).

The three checks below make the mismatch concrete with exact integer arithmetic.
"""

from itertools import combinations
from math import ceil
from fractions import Fraction
import math


def sq(p, q):
    return (p[0] - q[0]) ** 2 + (p[1] - q[1]) ** 2


def R(pts, i):
    return len({sq(pts[i], pts[j]) for j in range(len(pts)) if j != i})


def file_g_of_config(pts):
    """numDistinctRValues: how many DISTINCT R-values the config has (the file's g target)."""
    return len({R(pts, i) for i in range(len(pts))})


def real_maxR(pts):
    """max_{p} R(p): the quantity the REAL #653 lower-bounds (under no-4-concyclic)."""
    return max(R(pts, i) for i in range(len(pts)))


# ---------------------------------------------------------------------------
# (A) The file's g(n) already EXCEEDS the Erdős–Fishburn 3/8 lower bound.
#     The equally-spaced collinear set gives g(n) >= ceil(n/2) = 0.5 n > 0.375 n.
#     If the file's g were the real f(n), a trivial construction would beat the
#     published Erdős–Fishburn lower bound by a constant factor — impossible.
#     Hence file-g is provably NOT the f(n) of Erdős #653.
# ---------------------------------------------------------------------------
def check_g_exceeds_erdos_fishburn():
    print("(A) file g(n) >= ceil(n/2) = 0.5 n already exceeds Erdős–Fishburn 3/8 n:")
    ok = True
    for n in (8, 12, 20, 40, 100):
        collinear = [(i, 0) for i in range(n)]
        d = file_g_of_config(collinear)  # = ceil(n/2)
        ef = Fraction(3, 8) * n
        beats = d > ef
        ok &= beats and d == ceil(n / 2)
        print(f"  n={n:3d}: collinear D={d}=ceil(n/2)={ceil(n/2)} ; 3/8 n={float(ef):.1f}"
              f" ; file-g exceeds E-F: {beats}")
    print(f"  => file-g cannot be the real f(n) (a trivial set beats a published lower bound): {ok}\n")
    return ok


# ---------------------------------------------------------------------------
# (B) The 'no four concyclic' hypothesis is ESSENTIAL and ABSENT from the file.
#     The regular n-gon has all n points concyclic, so it is EXCLUDED from the
#     real #653. There every point sees only floor(n/2) distinct distances, so
#     without the exclusion the real min–max f(n) would collapse to ~n/2. The
#     file imposes no such rule, confirming it does not model the real problem.
# ---------------------------------------------------------------------------
def regpoly(n):
    return [(math.cos(2 * math.pi * k / n), math.sin(2 * math.pi * k / n)) for k in range(n)]


def Rfloat(pts, i):
    ds = {round(((pts[i][0] - pts[j][0]) ** 2 + (pts[i][1] - pts[j][1]) ** 2), 9)
          for j in range(len(pts)) if j != i}
    return len(ds)


def check_concyclic_obstruction():
    print("(B) regular n-gon = all-concyclic obstruction the real #653 EXCLUDES:")
    ok = True
    for n in (6, 8, 10, 12):
        p = regpoly(n)
        mr = max(Rfloat(p, i) for i in range(n))
        ok &= (mr == n // 2)
        print(f"  regular {n}-gon: every point R=floor(n/2)={n // 2}, max-R={mr}."
              f" Excluded by 'no four concyclic'; file has no such hypothesis.")
    print(f"  => the forbidden-configuration hypothesis is missing from the formalization: {ok}\n")
    return ok


# ---------------------------------------------------------------------------
# (C) The two quantities genuinely DISAGREE on concrete configs (not just in
#     definition). For the same point set, file-g (#distinct R-values) and the
#     real per-point max-R are different numbers.
# ---------------------------------------------------------------------------
def check_quantities_disagree():
    print("(C) file-g (#distinct R-values) vs real max-R disagree on the same configs:")
    configs = {
        "collinear n=6": [(i, 0) for i in range(6)],
        "L-witness n=4": [(0, 0), (0, 1), (0, 2), (1, 1)],
        "square n=4": [(0, 0), (1, 0), (0, 1), (1, 1)],
    }
    any_diff = False
    for name, pts in configs.items():
        g = file_g_of_config(pts)
        mr = real_maxR(pts)
        diff = g != mr
        any_diff |= diff
        print(f"  {name:16s}: file-g={g}, real max-R={mr}  -> differ: {diff}")
    print(f"  => the two functions are not equal even on small examples: {any_diff}\n")
    return any_diff


if __name__ == "__main__":
    print("=" * 72)
    print("Erdős #653 — gallery formalization mis-states the problem (correctness check)")
    print("=" * 72)
    a = check_g_exceeds_erdos_fishburn()
    b = check_concyclic_obstruction()
    c = check_quantities_disagree()
    print("Summary:")
    print(f"  (A) file-g exceeds the cited 3/8 lower bound  => file-g != f(n) : {a}")
    print(f"  (B) no-4-concyclic hypothesis missing from file               : {b}")
    print(f"  (C) file-g and real max-R disagree on concrete configs        : {c}")
    print()
    print("CONCLUSION: `Erdos653Problem.lean` formalizes a DIFFERENT quantity than")
    print("Erdős #653 (max #distinct R-values, no concyclic rule) and the cited")
    print("csizmadia_bound / upper_bound axioms are results about f(n), not this g(n).")
