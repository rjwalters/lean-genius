#!/usr/bin/env python3
"""
Erdős Problem #733 — OQ-01: the limiting constant  λ = lim_{n→∞} log f(n)/√n.

f(n) = number of "line-compatible" sequences for an n-point planar configuration:
the sorted multiset of point-counts over its rich lines (lines with ≥2 points).
Szemerédi–Trotter (1983) gives f(n) = exp(Θ(√n)); the constant λ is OPEN.

----------------------------------------------------------------------------
STRUCTURAL REFORMULATION (this session)
----------------------------------------------------------------------------
The point-count of every rich line is recorded.  The 2-point lines are exactly
the pairs not covered by a ≥3 line, so their number is

    #(2-lines)  =  C(n,2)  −  Σ_{≥3 lines L} C(|L|, 2),

which is DETERMINED by n and the multiset of ≥3-line sizes.  Hence the whole
line-compatible sequence is a function of the multiset of ≥3-line sizes, and

    f(n)  =  #{ multisets M of integers ≥3 realizable as the exact ≥3-rich-line
               sizes of some n-point configuration }.

A multiset M is realizable with n points iff its minimum realization budget
μ(M) (fewest points whose ≥3-rich lines have exactly the sizes in M, all other
rich lines carrying 2 points) satisfies μ(M) ≤ n — extra points go in general
position as 2-lines.  So  f(n) = #{ M : μ(M) ≤ n }.

----------------------------------------------------------------------------
A COMPUTABLE LOWER BOUND  G(n) ≤ f(n)
----------------------------------------------------------------------------
μ(M) is itself a hard incidence-geometry optimisation (maximise point sharing
among the lines).  We use three explicit, always-realizable constructions and
take the cheapest; this OVER-estimates μ, hence UNDER-counts, giving a rigorous
lower bound.  For M = {a_1,…,a_k} (each a_i ≥ 3, k parts):

  (disjoint)   each part on its own generic line ............  Σ a_i
  (pencil)     all k lines concurrent at one point O ........  Σ a_i − (k−1)
  (complete)   k generic lines, ALL C(k,2) pairwise           Σ a_i − C(k,2)
               intersections used as shared points              (needs a_i ≥ k−1)

    μ*(M) = min of the applicable budgets,   G(n) = #{ M : μ*(M) ≤ n }.

Because every counted M has an explicit ≤ n-point realization, G(n) ≤ f(n)
RIGOROUSLY.  This script REALIZES each construction in exact ℚ arithmetic,
recomputes the rich-line multiset from scratch, and confirms it equals the
predicted sequence with no accidental extra ≥3 line — so each G(n) below is a
verified lower bound.

----------------------------------------------------------------------------
RESULTS
----------------------------------------------------------------------------
  • G(n) = f(n) EXACTLY for n = 3,4,5,6  (2, 3, 5, 9): the three elementary
    constructions already realize every line-compatible sequence at small n.
    - n=5: the surplus over the disjoint bound (f(5)=5 > Q(5)=4) is the PENCIL
      [3,3] — two 3-point lines sharing a point (budget 5, not 6).  G is tight.
    - n=6: the surplus includes the COMPLETE QUADRILATERAL [3,3,3,3] — four
      generic lines, 6 intersection points (budget 6), which the disjoint and
      pencil families both miss.
  • For n ≥ 7, G(n) extends rigorous lower bounds well beyond the prior
    disjoint bound Q(n):
        n:        7   8   9  10  11  12
        G(n) ≥:  14  21  31  45  63  87
        Q(n)  :   8  11  15  20  26  35   (prior session's lower bound)
  • ASYMPTOTICS (honesty): G ≥ Q so G's rate ≥ π√(2/3); the complete-arrangement
    contribution alone has a strictly SMALLER exponential rate (parts forced
    ≥ k−1 is rigid), so the disjoint family still dominates as n→∞ and G(n) does
    NOT improve the asymptotic constant beyond  λ ≥ π√(2/3) ≈ 2.5651.  The gap
    to the true (open) λ needs the full realizability structure
    (Szemerédi–Trotter), exactly as the upper side does.

Run:  python3 verify_arrangement_lower.py
"""

from fractions import Fraction as Fr
from itertools import combinations
from functools import lru_cache
from math import comb, pi, sqrt, log

# ---------------------------------------------------------------------------
# Exact geometry
# ---------------------------------------------------------------------------

def line_key(p, q):
    """Canonical exact key for the line through distinct p, q: A x + B y = C
       with the first nonzero of (A,B) normalised to 1."""
    A = q[1] - p[1]
    B = p[0] - q[0]
    C = A * p[0] + B * p[1]
    if A != 0:
        B, C, A = B / A, C / A, Fr(1)
    elif B != 0:
        C, B = C / B, Fr(1)
    return (A, B, C)

def rich_line_multiset(points):
    """Sorted-descending multiset of point-counts over lines with ≥2 points."""
    counts = {}
    for i, j in combinations(range(len(points)), 2):
        counts.setdefault(line_key(points[i], points[j]), set()).update((i, j))
    return tuple(sorted((len(s) for s in counts.values() if len(s) >= 2),
                        reverse=True))

def big_lines(points):
    """Sorted-ascending multiset of point-counts over lines with ≥3 points."""
    counts = {}
    for i, j in combinations(range(len(points)), 2):
        counts.setdefault(line_key(points[i], points[j]), set()).update((i, j))
    return tuple(sorted(len(s) for s in counts.values() if len(s) >= 3))

# ---------------------------------------------------------------------------
# Budget formula and G(n)
# ---------------------------------------------------------------------------

def mu_star(M):
    """min realization budget over {disjoint, pencil, complete arrangement}."""
    if not M:
        return 0
    k = len(M); s = sum(M)
    cands = [s, s - (k - 1)]               # disjoint, single pencil
    if min(M) >= k - 1:                    # complete generic arrangement
        cands.append(s - comb(k, 2))
    return min(cands)

def best_construction(M):
    """Return the construction name achieving μ*(M)."""
    if not M:
        return "empty"
    k = len(M); s = sum(M); m = mu_star(M)
    if min(M) >= k - 1 and s - comb(k, 2) == m:
        return "complete"
    if s - (k - 1) == m and k >= 2:
        return "pencil"
    return "disjoint"

def gen_multisets(maxsum):
    res = []
    def rec(remaining, least, cur):
        res.append(tuple(cur))
        for p in range(least, remaining + 1):
            cur.append(p); rec(remaining - p, p, cur); cur.pop()
    rec(maxsum, 3, [])
    return res

def G_multisets(n):
    """All multisets M (parts ≥3) with μ*(M) ≤ n."""
    maxsave = comb(int((2 * n) ** 0.5) + 3, 2)   # save ≤ C(k,2); generous bound
    return [M for M in gen_multisets(n + maxsave) if mu_star(M) <= n]

def G(n):
    return len(G_multisets(n))

@lru_cache(None)
def _p_minpart(s, mn, lo):
    if s == 0:
        return 1
    return sum(_p_minpart(s - a, a, lo) for a in range(max(mn, lo), s + 1))

def Q(n):
    """#{partitions of any s≤n into parts ≥3}  (prior disjoint-line bound)."""
    return sum(_p_minpart(s, 3, 3) for s in range(0, n + 1))

def P(n):
    """#{partitions into parts ≥2 of sum ≤ n−1}  (single-pencil bound)."""
    return sum(_p_minpart(s, 2, 2) for s in range(0, max(0, n)))

# ---------------------------------------------------------------------------
# Exact realizers (return list of ℚ points, or None on accidental degeneracy)
# ---------------------------------------------------------------------------

def _add_fillers(pts, count, shift):
    """Append `count` points on a far parabola y=x^2 (no 3 collinear among them
       and generically nothing collinear with the existing arrangement)."""
    base = 10000 + 31 * shift
    for t in range(count):
        x = Fr(base + 7 * t, 1)
        pts.append((x, x * x))

def realize_disjoint(M, n, shift):
    pts = []
    for i, a in enumerate(M):
        m, b = Fr(2 * i + 1), Fr(7 * i + 3)
        for t in range(a):
            x = Fr(shift * (i + 1) + t * (len(M) + 1) + 1)
            pts.append((x, m * x + b))
    _add_fillers(pts, n - sum(M), shift)
    return pts

def realize_pencil(M, n, shift):
    O = (Fr(0), Fr(0))
    pts = [O]
    used = 1
    for i, a in enumerate(M):
        slope = Fr(2 * i + 1 + shift)          # distinct slopes through O
        for t in range(1, a):                  # a-1 further points on the line
            # stagger x per line so no two lines share an x (spurious vertical
            # line) and points on different lines are generic
            x = Fr(1 + shift + t + 100 * i)
            pts.append((x, slope * x))
            used += 1
    _add_fillers(pts, n - used, shift)
    return pts

def realize_complete(M, n, shift):
    """k generic lines L_i: y = m_i x + c_i; use all C(k,2) intersections as
       shared points, plus private points on each line to reach size a_i."""
    k = len(M)
    if k == 0:
        pts = []; _add_fillers(pts, n, shift); return pts
    if min(M) < k - 1:
        return None
    m = [Fr(i + 1 + shift) for i in range(k)]              # distinct slopes
    c = [Fr((i + 1) ** 2 + 3 * shift) for i in range(k)]   # distinct intercepts

    def inter(i, j):
        # m_i x + c_i = m_j x + c_j  ->  x = (c_j - c_i)/(m_i - m_j)
        x = (c[j] - c[i]) / (m[i] - m[j])
        return (x, m[i] * x + c[i])

    on_line = [[] for _ in range(k)]   # accumulate points on each line
    inter_pts = {}
    for i, j in combinations(range(k), 2):
        p = inter(i, j)
        inter_pts[(i, j)] = p
        on_line[i].append(p); on_line[j].append(p)
    # all intersections must be distinct (genericity)
    allpts = list(inter_pts.values())
    if len({(p[0], p[1]) for p in allpts}) != len(allpts):
        return None
    # add private points on each line to reach a_i
    pts = list(allpts)
    for i, a in enumerate(M):
        need = a - (k - 1)
        if need < 0:
            return None
        mi, ci = m[i], c[i]
        # stagger per-line so private points never share an x (would be a
        # spurious vertical rich line) and avoid aligning across lines
        added = 0; x = Fr(50 + 13 * shift + 101 * i)
        existing_x = {q[0] for q in on_line[i]}
        while added < need:
            if x not in existing_x:
                pts.append((x, mi * x + ci))
                existing_x.add(x); added += 1
            x += 1
    _add_fillers(pts, n - len(pts), shift)
    return pts

REALIZERS = {"disjoint": realize_disjoint, "pencil": realize_pencil,
             "complete": realize_complete}

def realize(M, n):
    """Realize M at exactly n points via the μ*-optimal construction; verify the
       ≥3-line multiset is exactly M.  Returns (points, sequence) or raises."""
    name = best_construction(M)
    if name == "empty":
        pts = []; _add_fillers(pts, n, 1)
        return pts, rich_line_multiset(pts)
    fn = REALIZERS[name]
    for shift in range(1, 80):
        pts = fn(M, n, shift)
        if pts is None or len(pts) != n:
            continue
        if big_lines(pts) == tuple(sorted(M)):
            return pts, rich_line_multiset(pts)
    raise RuntimeError(f"could not cleanly realize M={M} via {name} at n={n}")

# ---------------------------------------------------------------------------
# Verification driver
# ---------------------------------------------------------------------------

def predicted_sequence(M, n):
    twos = comb(n, 2) - sum(comb(a, 2) for a in M)
    return tuple(sorted(list(M) + [2] * twos, reverse=True))

def verify_small(n):
    """Realize every M counted in G(n); confirm each matches its prediction and
       all realized sequences are distinct  ⇒  G(n) is a verified lower bound."""
    Ms = G_multisets(n)
    realized = {}
    bad = 0
    for M in Ms:
        _, seq = realize(M, n)
        pred = predicted_sequence(M, n)
        if seq != pred:
            bad += 1
            print(f"   MISMATCH M={M}: realized {seq} != predicted {pred}")
        realized.setdefault(seq, []).append(M)
    distinct = len(realized)
    collisions = {k: v for k, v in realized.items() if len(v) > 1}
    ok = (bad == 0 and distinct == len(Ms) and not collisions)
    flag = "OK " if ok else "FAIL"
    print(f"  [{flag}] n={n:2d}: G(n)={len(Ms):3d}  distinct_realized={distinct:3d}"
          f"  mismatches={bad}  collisions={len(collisions)}  (Q={Q(n)}, P={P(n)})")
    for k, v in collisions.items():
        print(f"     COLLISION seq={k} from {v}")
    return ok

def main():
    print("=" * 74)
    print("Erdős #733 OQ-01: arrangement lower bound  G(n) ≤ f(n)")
    print("=" * 74)

    print("\n[1] Exact-arithmetic realization of every M counted by G(n).")
    all_ok = True
    for n in range(3, 13):
        all_ok &= verify_small(n)
    print(f"\n  [1] {'ALL REALIZATIONS VERIFIED' if all_ok else 'FAILURES PRESENT'}"
          "  ⇒  G(n) is a rigorous lower bound on f(n).")

    print("\n[2] G(n) vs exact f(n) (f known only for n≤6) and prior bounds.")
    fdata = {3: 2, 4: 3, 5: 5, 6: 9}
    print(f"   {'n':>3} {'G(n)':>6} {'f(n)':>6} {'P(n)':>6} {'Q(n)':>6}  note")
    for n in range(3, 13):
        g = G(n); fd = fdata.get(n)
        note = ("= f(n)  ✓" if fd is not None and g == fd else
                ("≠ f(n)!" if fd is not None else "lower bound on f(n)"))
        print(f"   {n:>3} {g:>6} {str(fd) if fd is not None else '?':>6} "
              f"{P(n):>6} {Q(n):>6}  {note}")
    # hard assertions on the verified small cases
    for n, fv in fdata.items():
        assert G(n) == fv, f"G({n})={G(n)} != f({n})={fv}"
    print("   PASS: G(n) = f(n) for n = 3,4,5,6.")

    print("\n[3] Witness constructions for the surplus over the disjoint bound:")
    for M in [(3, 3), (3, 3, 3), (3, 3, 3, 3)]:
        n0 = mu_star(M)
        pts, seq = realize(M, n0)
        print(f"   M={M}  via {best_construction(M):8s}  μ*={n0}  "
              f"realized ≥3-lines={big_lines(pts)}")

    print("\n[4] CONCLUSION")
    print("   • f(n) = #{realizable multisets of ≥3-line sizes}; the 2-line count")
    print("     is forced, so the whole sequence is a function of that multiset.")
    print("   • G(n) (disjoint ∨ pencil ∨ complete-arrangement budgets) is a")
    print("     verified lower bound that EQUALS f(n) for n≤6 and extends rigorous")
    print("     lower bounds for n≥7 (f(7)≥14, f(8)≥21, …, f(12)≥87).")
    print("   • Asymptotic constant unchanged: G ≥ Q ⇒ λ ≥ π√(2/3) ≈ 2.5651; the")
    print("     complete-arrangement family has a strictly smaller rate, so it does")
    print("     not raise the constant.  The matching upper constant stays OPEN.")
    return 0 if all_ok else 1

if __name__ == "__main__":
    raise SystemExit(main())
