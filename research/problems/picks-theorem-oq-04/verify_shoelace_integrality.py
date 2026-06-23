#!/usr/bin/env python3
"""
Durable, build-free verification for picks-theorem-oq-04:

    "Shoelace formula and its integrality bridge to Pick's theorem"

The gallery already proves the *triangle* shoelace formula and its integrality
(`PicksTheoremOQ01.lean: shoelaceTriangle`, `PicksTheoremOQ01OQ01OQ01.lean:
twiceArea = |det|`).  OQ-04 asks for the *general simple n-gon* statement and the
"integrality bridge": that twice the shoelace area is always an INTEGER for a
lattice polygon, hence Area in (1/2)Z, matching the denominator structure of
Pick's formula  Area = i + b/2 - 1.

This script checks, with EXACT integer arithmetic (no floats), four claims on a
battery of lattice polygons (convex, non-convex, with collinear boundary points):

  (I)   INTEGRALITY:  S := sum_i (x_i*y_{i+1} - x_{i+1}*y_i)  is an integer and
        2*Area = |S|.  So Area is always a half-integer.
  (II)  FAN-TRIANGULATION BRIDGE:  the general shoelace sum S equals the sum, over
        the fan triangles (v0, v_i, v_{i+1}), of the per-triangle determinant
        cross2(v0, v_i, v_{i+1}).  This is the exact lift of the proven triangle
        formula to general n via `picks_additivity` / the partition-sum identity.
  (III) TRIANGLE REDUCTION:  for n = 3 the general formula reproduces the existing
        `shoelaceTriangle` value 1/2 |x1(y2-y3)+x2(y3-y1)+x3(y1-y2)|.
  (IV)  PICK AGREEMENT:  |S| == 2*i + b - 2, where i,b are the interior / boundary
        lattice-point counts computed independently by exact enumeration.  This is
        the integrality bridge made concrete: Pick's i + b/2 - 1 has the SAME
        twice-area integer |S|.

Run: python3 verify_shoelace_integrality.py
"""

from math import gcd
from itertools import combinations
import random


# ----------------------------------------------------------------------
# Exact geometric primitives (all integer arithmetic)
# ----------------------------------------------------------------------

def cross2(o, a, b):
    """Twice the signed area of triangle (o, a, b) = (a-o) x (b-o)."""
    return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])


def shoelace_sum(poly):
    """S = sum_i (x_i*y_{i+1} - x_{i+1}*y_i)  (signed, twice the signed area)."""
    n = len(poly)
    s = 0
    for i in range(n):
        x1, y1 = poly[i]
        x2, y2 = poly[(i + 1) % n]
        s += x1 * y2 - x2 * y1
    return s


def fan_sum(poly):
    """Sum of per-triangle determinants from apex v0: the fan triangulation."""
    v0 = poly[0]
    s = 0
    for i in range(1, len(poly) - 1):
        s += cross2(v0, poly[i], poly[i + 1])
    return s


def shoelace_triangle_twice(t):
    """Matches Lean `shoelaceTriangle` numerator: |x1(y2-y3)+x2(y3-y1)+x3(y1-y2)|."""
    (x1, y1), (x2, y2), (x3, y3) = t
    return abs(x1 * (y2 - y3) + x2 * (y3 - y1) + x3 * (y1 - y2))


def boundary_count(poly):
    """Number of lattice points on the boundary = sum of gcd(|dx|,|dy|) per edge."""
    n = len(poly)
    b = 0
    for i in range(n):
        x1, y1 = poly[i]
        x2, y2 = poly[(i + 1) % n]
        b += gcd(abs(x2 - x1), abs(y2 - y1))
    return b


def on_segment(p, a, b):
    """Is lattice point p on the closed segment [a,b]? (exact)"""
    if cross2(a, b, p) != 0:
        return False
    return (min(a[0], b[0]) <= p[0] <= max(a[0], b[0]) and
            min(a[1], b[1]) <= p[1] <= max(a[1], b[1]))


def on_boundary(p, poly):
    n = len(poly)
    return any(on_segment(p, poly[i], poly[(i + 1) % n]) for i in range(n))


def winding_number(p, poly):
    """Integer winding number of poly around p (p not on boundary)."""
    n = len(poly)
    wn = 0
    for i in range(n):
        a = poly[i]
        b = poly[(i + 1) % n]
        if a[1] <= p[1]:
            if b[1] > p[1] and cross2(a, b, p) > 0:
                wn += 1
        else:
            if b[1] <= p[1] and cross2(a, b, p) < 0:
                wn -= 1
    return wn


def interior_count(poly):
    """Strictly-interior lattice points by exact bounding-box enumeration."""
    xs = [v[0] for v in poly]
    ys = [v[1] for v in poly]
    cnt = 0
    for x in range(min(xs), max(xs) + 1):
        for y in range(min(ys), max(ys) + 1):
            p = (x, y)
            if on_boundary(p, poly):
                continue
            if winding_number(p, poly) != 0:
                cnt += 1
    return cnt


def is_simple(poly):
    """Reject self-intersecting / degenerate polygons (so Pick applies)."""
    n = len(poly)
    if n < 3:
        return False
    # no repeated vertices
    if len(set(poly)) != n:
        return False
    # no zero-length / collinear-spike: consecutive edges not anti-parallel onto same line is fine;
    # main requirement: non-adjacent edges must not cross or touch.
    edges = [(poly[i], poly[(i + 1) % n]) for i in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            if j == i:
                continue
            a, b = edges[i]
            c, d = edges[j]
            adjacent = (j == (i + 1) % n) or (i == (j + 1) % n)
            if adjacent:
                # shared endpoint allowed; ensure they don't overlap collinearly
                continue
            if segments_intersect(a, b, c, d):
                return False
    # nonzero area
    return shoelace_sum(poly) != 0


def segments_intersect(a, b, c, d):
    d1 = cross2(c, d, a)
    d2 = cross2(c, d, b)
    d3 = cross2(a, b, c)
    d4 = cross2(a, b, d)
    if ((d1 > 0) != (d2 > 0)) and ((d3 > 0) != (d4 > 0)) and d1 != 0 and d2 != 0 and d3 != 0 and d4 != 0:
        return True
    for (p, q, r) in [(c, d, a), (c, d, b), (a, b, c), (a, b, d)]:
        if cross2(p, q, r) == 0 and on_segment(r, p, q):
            return True
    return False


# ----------------------------------------------------------------------
# Checks
# ----------------------------------------------------------------------

def check_polygon(poly, name):
    """Run all four claims on one (CCW, simple) polygon. Returns dict of bools."""
    S = shoelace_sum(poly)
    res = {}

    # (I) integrality: S is an int (true by construction) and 2*Area = |S|
    twice_area = abs(S)
    res["I_integral"] = isinstance(S, int) and twice_area >= 0

    # (II) fan bridge
    res["II_fan"] = (S == fan_sum(poly))

    # (III) triangle reduction (only meaningful for n = 3)
    if len(poly) == 3:
        res["III_tri"] = (abs(S) == shoelace_triangle_twice(poly))
    else:
        res["III_tri"] = None  # not applicable

    # (IV) Pick agreement: |S| == 2 i + b - 2
    i = interior_count(poly)
    b = boundary_count(poly)
    res["IV_pick"] = (twice_area == 2 * i + b - 2)
    res["_data"] = (S, i, b, twice_area)
    return res


def ccw(poly):
    return poly if shoelace_sum(poly) > 0 else poly[::-1]


def random_convex_polygon(rng, k, span=8):
    """Random convex lattice polygon: take a random point set, use convex hull."""
    pts = set()
    while len(pts) < k + 3:
        pts.add((rng.randint(-span, span), rng.randint(-span, span)))
    pts = list(pts)
    hull = convex_hull(pts)
    return hull if len(hull) >= 3 else None


def convex_hull(points):
    pts = sorted(set(points))
    if len(pts) <= 2:
        return pts
    def half(pts):
        h = []
        for p in pts:
            while len(h) >= 2 and cross2(h[-2], h[-1], p) <= 0:
                h.pop()
            h.append(p)
        return h
    lower = half(pts)
    upper = half(pts[::-1])
    return lower[:-1] + upper[:-1]


def main():
    rng = random.Random(20260614)

    fixtures = {
        "unit_triangle (0,0)(1,0)(0,1)": [(0, 0), (1, 0), (0, 1)],
        "right_triangle (0,0)(3,0)(0,3)": [(0, 0), (3, 0), (0, 3)],
        "rectangle 3x4": [(0, 0), (3, 0), (3, 4), (0, 4)],
        "L_shape (nonconvex)": [(0, 0), (4, 0), (4, 2), (2, 2), (2, 4), (0, 4)],
        "pentagon": [(0, 0), (4, 0), (5, 3), (2, 5), (-1, 3)],
        "collinear_edge_quad": [(0, 0), (4, 0), (4, 2), (0, 2)],  # boundary pts on edges
        "big_triangle (0,0)(7,2)(3,6)": [(0, 0), (7, 2), (3, 6)],
        "zigzag_hex (nonconvex)": [(0, 0), (3, 1), (6, 0), (5, 3), (3, 2), (1, 3)],
    }

    all_ok = True
    print("=" * 78)
    print("picks-theorem-oq-04  —  general n-gon shoelace integrality + Pick bridge")
    print("=" * 78)
    header = f"{'polygon':32s} {'n':>2s} {'S':>6s} {'i':>4s} {'b':>4s}  I  II III IV"
    print(header)
    print("-" * 78)

    def fmt(v):
        return " ok" if v is True else ("  -" if v is None else "XXX")

    for name, poly in fixtures.items():
        if not is_simple(poly):
            print(f"{name:32s}  SKIPPED (not simple)")
            continue
        poly = ccw(poly)
        r = check_polygon(poly, name)
        S, i, b, ta = r["_data"]
        line = (f"{name:32s} {len(poly):2d} {S:6d} {i:4d} {b:4d} "
                f"{fmt(r['I_integral'])}{fmt(r['II_fan'])}{fmt(r['III_tri'])}{fmt(r['IV_pick'])}")
        print(line)
        for k in ("I_integral", "II_fan", "IV_pick"):
            if r[k] is not True:
                all_ok = False
        if r["III_tri"] is False:
            all_ok = False

    # Random convex battery
    print("-" * 78)
    print("Random convex lattice polygons (exact):")
    rc_ok = 0
    rc_total = 0
    for _ in range(400):
        poly = random_convex_polygon(rng, rng.randint(0, 8))
        if poly is None or not is_simple(poly):
            continue
        poly = ccw(poly)
        r = check_polygon(poly, "rand")
        rc_total += 1
        ok = (r["I_integral"] is True and r["II_fan"] is True and r["IV_pick"] is True)
        if ok:
            rc_ok += 1
        else:
            all_ok = False
            print("  MISMATCH:", poly, r["_data"], r)
    print(f"  {rc_ok}/{rc_total} random convex polygons pass all of (I),(II),(IV)")

    print("=" * 78)
    print("RESULT:", "ALL CHECKS PASS" if all_ok else "FAILURES PRESENT")
    print("=" * 78)
    return 0 if all_ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
