#!/usr/bin/env python3
"""
Durable numerical verification for Erdős #101 OQ-01 (four-point lines are o(n²)?).

This script grounds — independently of the Lean build (Docker) — the two
*proved, unconditional* arithmetic/combinatorial facts that the gallery file
`proofs/Proofs/Erdos101OQ01.lean` (and its parent `Erdos101Problem.lean`) rely
on, plus the surrogate Θ(n²) arithmetic underlying the in-flight reverse-IsBigO
work (PR #23389).

It does NOT attempt the two genuinely OPEN sorries:
  * `erdos_101_oq_01`              — the $100 o(n²) conjecture itself
  * `solymosi_stojakovic_lower_bound` — the Ω(n^{2−C/√log n}) finite-field construction

What is verified here:

  (A) `improved_upper_bound` pair-packing inequality
        6 · (#4-point collinear subsets) ≤ C(n,2)
      hence   fourPointLineCount(P) ≤ ⌊n(n-1)/12⌋
      brute-forced over random rational-coordinate no-five-collinear point sets
      AND structured grids.

  (B) The surrogate Θ(n²) arithmetic for `maxFourPointLines n = n(n-1)//12`:
        forward  maxFourPointLines n ≤ n²          (constant 1, all n)
        reverse  n² ≤ 24 · maxFourPointLines n     (constant 24, n ≥ 6)
      via the two ℕ-floor lemmas the Lean proof leans on:
        floor lower bound      a ≤ 12·(a//12) + 11
        residual (n≥6)         n² ≤ 2n² − 2n − 22   ⇔ (n−6)(n+4) ≥ 22−24 ... see below

  (C) A concrete real-plane lower-bound *witness*: the 4×4 integer grid has
      exactly 10 lines of exactly four points and NO five collinear, so the
      four-point-line count is genuinely positive and the elementary bound is
      not vacuous. (This is a witness, not the SS construction.)

Run:  python3 verify_bounds.py
Exit code 0 ⇔ all checks pass.
"""

from __future__ import annotations
import itertools
import math
import random
from fractions import Fraction
from collections import defaultdict

random.seed(101)  # deterministic


# ---------------------------------------------------------------------------
# Geometry primitives over exact rationals (no floating point).
# ---------------------------------------------------------------------------

def collinear(a, b, c):
    """Exact collinearity test via the cross product of (b−a) and (c−a)."""
    (ax, ay), (bx, by), (cx, cy) = a, b, c
    return (bx - ax) * (cy - ay) - (by - ay) * (cx - ax) == 0


def maximal_collinear_lines(points):
    """Return the set of maximal collinear subsets (as frozensets of indices).

    Two points determine a line; we group all points by the line they span,
    using an exact normalized line key, then return the point-index sets.
    """
    n = len(points)
    line_members = defaultdict(set)
    for i, j in itertools.combinations(range(n), 2):
        line_members[_line_key(points[i], points[j])].update((i, j))
    # Dedup: distinct (i,j) on the same line produce the same key, so the
    # members sets already coincide. Collect unique frozensets.
    seen = set()
    out = []
    for members in line_members.values():
        fs = frozenset(members)
        if fs not in seen:
            seen.add(fs)
            out.append(fs)
    return out


def _line_key(p, q):
    """Exact canonical key for the line through distinct points p, q.

    Line: A x + B y + C = 0 with (A,B,C) = (qy−py, px−qx, qx·py − px·qy),
    normalized by dividing by gcd and fixing a sign convention.
    """
    (px, py), (qx, qy) = p, q
    A = qy - py
    B = px - qx
    C = qx * py - px * qy
    # Work over integers if possible; otherwise clear denominators.
    A, B, C = _clear_denoms(A, B, C)
    g = math.gcd(math.gcd(abs(A), abs(B)), abs(C))
    if g:
        A, B, C = A // g, B // g, C // g
    # sign convention: first nonzero of (A,B,C) positive
    for v in (A, B, C):
        if v != 0:
            if v < 0:
                A, B, C = -A, -B, -C
            break
    return (A, B, C)


def _clear_denoms(*vals):
    fracs = [Fraction(v) for v in vals]
    lcm = 1
    for f in fracs:
        lcm = lcm * f.denominator // math.gcd(lcm, f.denominator)
    return tuple(int(f * lcm) for f in fracs)


def four_point_line_count(points):
    """Number of 4-element collinear subsets = #lines with exactly 4 points
    (under the no-five-collinear regime, each contributes exactly one)."""
    count = 0
    for members in maximal_collinear_lines(points):
        k = len(members)
        # number of 4-subsets that are collinear on this maximal line
        if k >= 4:
            count += math.comb(k, 4)
    return count


def max_line_multiplicity(points):
    return max((len(m) for m in maximal_collinear_lines(points)), default=0)


# ---------------------------------------------------------------------------
# (A) improved_upper_bound : 6·count ≤ C(n,2)  and  count ≤ ⌊n(n-1)/12⌋
# ---------------------------------------------------------------------------

def check_improved_upper_bound_on(points, label):
    n = len(points)
    mult = max_line_multiplicity(points)
    if mult >= 5:
        return None  # not a no-five-collinear configuration; bound doesn't apply
    count = four_point_line_count(points)
    pairs = math.comb(n, 2)
    floor_bound = n * (n - 1) // 12
    ok_pack = 6 * count <= pairs
    ok_floor = count <= floor_bound
    assert ok_pack, f"PAIR-PACK VIOLATED [{label}] n={n}: 6*{count}={6*count} > C(n,2)={pairs}"
    assert ok_floor, f"FLOOR BOUND VIOLATED [{label}] n={n}: {count} > {floor_bound}"
    return (n, count, floor_bound, mult)


def random_no5_pointset(n, lo=0, hi=12, tries=2000):
    """Random integer-coordinate set of n points with no five collinear."""
    for _ in range(tries):
        pts = set()
        while len(pts) < n:
            pts.add((random.randint(lo, hi), random.randint(lo, hi)))
        pts = list(pts)
        if max_line_multiplicity(pts) < 5:
            return pts
    return None


def part_A():
    print("== (A) improved_upper_bound pair-packing  6·count ≤ C(n,2) ⟹ count ≤ ⌊n(n-1)/12⌋ ==")
    checked = 0
    witnesses_with_4lines = 0
    # random configurations
    for n in range(4, 13):
        for _ in range(40):
            pts = random_no5_pointset(n)
            if pts is None:
                continue
            res = check_improved_upper_bound_on(pts, f"rand n={n}")
            if res:
                checked += 1
                if res[1] > 0:
                    witnesses_with_4lines += 1
    print(f"   random no-5-collinear configs checked: {checked} "
          f"(of which {witnesses_with_4lines} had ≥1 four-point line); all satisfy the bound")
    # structured grids 2x2 .. 4x4 (k=4 is the largest grid with no 5 collinear)
    for k in (2, 3, 4):
        pts = [(x, y) for x in range(k) for y in range(k)]
        res = check_improved_upper_bound_on(pts, f"{k}x{k} grid")
        if res:
            n, count, fb, mult = res
            print(f"   {k}x{k} grid: n={n}, four-point-line count={count}, "
                  f"⌊n(n-1)/12⌋={fb}, max collinear={mult}  ✓")
    print("   PASS\n")
    return checked


# ---------------------------------------------------------------------------
# (B) surrogate Θ(n²) arithmetic for maxFourPointLines n = n(n-1)//12
#     (the function behind PR #23389's reverse IsBigO)
# ---------------------------------------------------------------------------

def max_four_point_lines(n):
    return n * (n - 1) // 12


def part_B():
    print("== (B) surrogate Θ(n²): maxFourPointLines n = n(n-1)//12 ==")
    N = 5000
    # forward: maxFourPointLines n ≤ n²  (so it is O(n²) with constant 1)
    for n in range(0, N):
        assert max_four_point_lines(n) <= n * n, f"forward fail n={n}"
    # the ℕ-floor lower bound the Lean proof uses: a ≤ 12·(a//12) + 11
    for a in range(0, 100000):
        assert a <= 12 * (a // 12) + 11, f"floor lemma fail a={a}"
    # reverse: n² ≤ 24 · maxFourPointLines n  for n ≥ 6 (PR #23389 constant 24)
    bad = [n for n in range(6, N) if n * n > 24 * max_four_point_lines(n)]
    assert not bad, f"reverse (const 24, n≥6) fails at {bad[:5]}"
    # show it genuinely needs n ≥ 6: list small n where it would fail
    small_fail = [n for n in range(0, 6) if n * n > 24 * max_four_point_lines(n)]
    # residual identity used in the nlinarith step:  with a = n²−n (= n(n-1)),
    #   12·(a//12) ≥ a − 11, and  n² ≤ 2(n²−n) − 22  ⇔  (n−6)(n+4) ≥ 2  for the
    #   threshold; verify the clean factored form (n−6)(n+4) ≥ 0 ⟹ n²≥2n+24-... :
    for n in range(6, N):
        a = n * n - n
        assert 2 * a - 22 >= n * n, f"residual n²≤2n²−2n−22 fails n={n}"
        assert (n - 6) * (n + 4) >= 0, f"factor (n-6)(n+4)≥0 fails n={n}"
    print(f"   forward maxFourPointLines n ≤ n²: PASS for n<{N}")
    print(f"   floor lemma a ≤ 12·⌊a/12⌋+11: PASS for a<100000")
    print(f"   reverse n² ≤ 24·maxFourPointLines n (n≥6): PASS for n<{N}")
    print(f"   threshold confirmed: const-24 reverse bound fails for n∈{small_fail} (needs n≥6)")
    print(f"   residual n²≤2n²−2n−22 and factor (n−6)(n+4)≥0: PASS for 6≤n<{N}")
    print("   ⟹ maxFourPointLines is Θ(n²): the *elementary* bound is NOT o(n²);")
    print("     the open content of OQ-01 is a genuinely sub-quadratic refinement.\n")


# ---------------------------------------------------------------------------
# (C) concrete real-plane lower-bound witness: the 4x4 grid
# ---------------------------------------------------------------------------

def part_C():
    print("== (C) real-plane witness: 4×4 integer grid ==")
    pts = [(x, y) for x in range(4) for y in range(4)]
    n = len(pts)
    mult = max_line_multiplicity(pts)
    # enumerate maximal lines with exactly 4 points
    exactly4 = [m for m in maximal_collinear_lines(pts) if len(m) == 4]
    count = four_point_line_count(pts)
    assert mult == 4, f"grid should have max multiplicity 4, got {mult}"
    assert len(exactly4) == count, "all 4-lines are exactly-4 (no 5 collinear)"
    print(f"   n={n}, max collinear={mult} (no 5 collinear ✓)")
    print(f"   lines of exactly 4 points = {len(exactly4)}  (4 rows + 4 cols + 2 diagonals)")
    print(f"   four_point_line_count = {count}, elementary bound ⌊n(n-1)/12⌋ = {n*(n-1)//12}")
    # the bound is tight up to a constant here: 10 vs 20
    assert count == 10, f"expected 10 four-point lines on 4x4 grid, got {count}"
    print("   ⟹ positive Θ(1)-fraction of the upper bound is realised in ℝ²; the\n"
          "     elementary bound is non-vacuous.  (A super-linear ℝ² construction is\n"
          "     the SS lower bound, deferred — see solymosi_stojakovic_lower_bound.)\n")


def main():
    print("Erdős #101 OQ-01 — durable bound verification (Docker-free)\n")
    part_A()
    part_B()
    part_C()
    print("ALL CHECKS PASSED.")


if __name__ == "__main__":
    main()
