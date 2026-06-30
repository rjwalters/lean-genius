#!/usr/bin/env python3
"""
Erdős Problem #733 — OQ-01: the limiting constant  λ = lim_{n→∞} log f(n) / √n.

f(n) = number of "line-compatible" sequences for n points: the distinct sorted
multisets of point-counts over the rich lines (lines with ≥ 2 points) of an
n-point configuration in the plane.  Szemerédi–Trotter (1983) gives
f(n) = exp(Θ(√n)); the exact constant λ (if the limit exists) is OPEN.

This script makes the lower side of the constant EXPLICIT and rigorously
checks the underlying construction in exact rational arithmetic.

CLAIM (constructive lower bound):
    f(n)  ≥  Q(n) := #{ partitions of any s ≤ n into parts ≥ 3 }
and hence, by Hardy–Ramanujan,
    liminf log f(n)/√n  ≥  π·√(2/3) ≈ 2.5651.

Why parts ≥ 3:  place each part a (≥3) as a generic line carrying exactly a
points, and the remaining n−Σa points in general position.  Generically the
ONLY lines with ≥3 points are the chosen ones; every other rich line has
exactly 2 points.  The realized sequence is therefore
    [the parts ≥ 3]  ++  [2 repeated  C(n,2) − Σ C(a_i,2)  times],
which is determined by — and determines — the multiset of parts ≥ 3.
Distinct such multisets ⇒ distinct line-compatible sequences ⇒ f(n) ≥ Q(n).

We VERIFY this for small n by actually placing the points (exact ℚ
coordinates), recomputing the rich-line multiset from scratch, and confirming
(1) each construction realizes its predicted sequence and (2) the realized
sequences are pairwise distinct, so the count equals Q(n).

No external assumptions; pure exact arithmetic.  Run:  python3 verify_lower_constant.py
"""

from fractions import Fraction as Fr
from itertools import combinations
from math import comb, pi, sqrt, log

# ---------------------------------------------------------------------------
# Exact geometry helpers
# ---------------------------------------------------------------------------

def collinear(p, q, r):
    """Exact test: are points p,q,r collinear?  (cross product == 0)."""
    return (q[0]-p[0])*(r[1]-p[1]) - (q[1]-p[1])*(r[0]-p[0]) == 0

def line_key(p, q):
    """Canonical exact key (A,B,C) for the line through distinct p,q: A x + B y = C."""
    A = q[1] - p[1]
    B = p[0] - q[0]
    C = A*p[0] + B*p[1]
    # normalize sign and scale so the key is canonical
    # divide by gcd-like normalization using Fractions: make leading nonzero entry 1
    if A != 0:
        B, C, A = B/A, C/A, Fr(1)
    elif B != 0:
        C, B = C/B, Fr(1)
    return (A, B, C)

def rich_line_sequence(points):
    """Sorted list of point-counts over all lines containing ≥ 2 points."""
    counts = {}
    for i, j in combinations(range(len(points)), 2):
        k = line_key(points[i], points[j])
        counts.setdefault(k, set()).update((i, j))
    seq = sorted(len(s) for s in counts.values() if len(s) >= 2)
    return tuple(seq)

# ---------------------------------------------------------------------------
# Partition enumeration (parts ≥ 3) and Q(n)
# ---------------------------------------------------------------------------

def partitions_min_part(s, m):
    """All partitions of s into parts ≥ m, as sorted ascending tuples."""
    if s == 0:
        yield ()
        return
    def rec(remaining, least):
        if remaining == 0:
            yield ()
            return
        for part in range(least, remaining + 1):
            for tail in rec(remaining - part, part):
                yield (part,) + tail
    yield from rec(s, m)

def Q(n):
    """#{ partitions of any s in 0..n into parts ≥ 3 }."""
    total = 0
    for s in range(0, n + 1):
        total += sum(1 for _ in partitions_min_part(s, 3))
    return total

# ---------------------------------------------------------------------------
# Realize a construction in exact arithmetic
# ---------------------------------------------------------------------------

def realize(parts_ge3, n):
    """
    Place n points: the i-th part a_i (≥3) on its own generic line with a_i
    points; remaining n - Σ a_i points in general position.  Deterministic
    generic coordinates chosen on the parabola y = x^2 PLUS controlled
    collinear blocks, with a verified-genericity fallback search.

    Returns the list of exact-rational points, or raises if it cannot place
    a clean generic configuration (should not happen for the small sizes used).
    """
    s = sum(parts_ge3)
    assert s <= n
    filler = n - s

    # Strategy: pick distinct generic slopes/intercepts for the part-lines and
    # generic x-positions, scanning small integer parameters until the realized
    # incidence structure has NO unintended ≥3-collinearity.
    # We parametrize attempts by an integer "spread" to perturb coordinates.
    for spread in range(1, 60):
        pts = []
        ok = True
        # part lines: line i has slope = prime-ish distinct value, intercept distinct
        slopes = [Fr(2*i + 1, 1) for i in range(len(parts_ge3))]
        intercepts = [Fr(7*i + 3, 1) for i in range(len(parts_ge3))]
        for i, a in enumerate(parts_ge3):
            m, b = slopes[i], intercepts[i]
            for t in range(a):
                x = Fr(spread*(i + 1) + t*(len(parts_ge3) + 1) + 1, 1)
                y = m * x + b
                pts.append((x, y))
        # filler points on the parabola y = x^2 shifted far away (parabola: no 3 collinear)
        base = 1000 + spread
        for t in range(filler):
            x = Fr(base + t, 1)
            y = x * x          # parabola guarantees no 3 filler collinear
            pts.append((x, y))
        # verify: the ONLY ≥3-point lines are exactly the intended part-lines
        counts = {}
        for ii, jj in combinations(range(len(pts)), 2):
            k = line_key(pts[ii], pts[jj])
            counts.setdefault(k, set()).update((ii, jj))
        big = sorted(len(v) for v in counts.values() if len(v) >= 3)
        if big == sorted(parts_ge3):
            return pts
        # else accidental collinearity; retry with different spread
    raise RuntimeError(f"could not realize {parts_ge3} with n={n}")

# ---------------------------------------------------------------------------
# Verification driver
# ---------------------------------------------------------------------------

def predicted_sequence(parts_ge3, n):
    twos = comb(n, 2) - sum(comb(a, 2) for a in parts_ge3)
    return tuple(sorted(list(parts_ge3) + [2] * twos))

def verify_small(n):
    """Realize every parts≥3 construction with sum ≤ n; confirm each matches its
       prediction and that all realized sequences are distinct => count == Q(n)."""
    realized = {}
    constructions = []
    for s in range(0, n + 1):
        for parts in partitions_min_part(s, 3):
            constructions.append(parts)
    bad = 0
    for parts in constructions:
        pts = realize(parts, n)
        seq = rich_line_sequence(pts)
        pred = predicted_sequence(parts, n)
        match = (seq == pred)
        if not match:
            bad += 1
            print(f"   MISMATCH parts={parts}: realized {seq} != predicted {pred}")
        realized.setdefault(seq, []).append(parts)
    distinct = len(realized)
    collisions = {k: v for k, v in realized.items() if len(v) > 1}
    q = Q(n)
    print(f"  n={n:2d}: constructions={len(constructions):3d}  distinct_realized={distinct:3d}  Q(n)={q:3d}"
          f"  mismatches={bad}  collisions={len(collisions)}")
    if collisions:
        for k, v in collisions.items():
            print(f"     COLLISION seq={k} from {v}")
    ok = (bad == 0 and distinct == q and len(collisions) == 0)
    return ok, q

def asymptotics(nmax=4000):
    print("\n[2] Hardy–Ramanujan asymptotic check  log Q(n)/√n  ->  π√(2/3) ≈ "
          f"{pi*sqrt(2/3):.6f}")
    # Q(n) via DP on partitions into parts >= 3, then cumulative.
    # p3[s] = # partitions of s into parts >= 3
    p3 = [0]*(nmax+1); p3[0] = 1
    for part in range(3, nmax+1):
        for s in range(part, nmax+1):
            p3[s] += p3[s-part]
    cum = 0
    targets = [50, 100, 250, 500, 1000, 2000, 4000]
    for n in range(1, nmax+1):
        cum += p3[n]
        if n in targets:
            print(f"   n={n:5d}:  log Q(n)/√n = {log(cum)/sqrt(n):.5f}")
    print(f"   limit  π√(2/3) = {pi*sqrt(2/3):.5f}")

def main():
    print("=" * 70)
    print("Erdős #733 OQ-01: explicit lower bound on  λ = lim log f(n)/√n")
    print("=" * 70)
    print("\n[1] Exact-arithmetic verification: f(n) >= Q(n) and the")
    print("    parts-≥3 construction realizes Q(n) distinct sequences.")
    all_ok = True
    for n in range(4, 13):
        ok, _ = verify_small(n)
        all_ok = all_ok and ok
    print(f"\n  [1] {'ALL CHECKS PASSED' if all_ok else 'FAILURES PRESENT'}: "
          "construction is valid and injective (=> f(n) >= Q(n)).")
    asymptotics()
    print("\n[3] CONCLUSION")
    print("    f(n) >= Q(n) = exp((π√(2/3)+o(1))√n)  =>  liminf log f(n)/√n >= π√(2/3) ≈ 2.5651.")
    print("    This sharpens the gallery's 'lower_bound : ∃ c>0' to an EXPLICIT c.")
    print("    The matching upper constant (from Szemerédi–Trotter) remains OPEN.")
    return 0 if all_ok else 1

if __name__ == "__main__":
    raise SystemExit(main())
