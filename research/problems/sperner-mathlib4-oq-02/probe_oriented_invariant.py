#!/usr/bin/env python3
"""
Probe: which SIGNED/ORIENTED complementary-edge count is a parity invariant on the
n=2 hexagon triangulation of B^2?

Context (sperner-mathlib4-oq-02). The knowledge base already machine-checked
(`SpernerTuckerHexagon.count_parity_not_invariant`) that the RAW complementary-edge
count is NOT a mod-2 invariant for n=2 -- some antipodal labellings have an even
count, some odd. That is exactly why "count the target, show it is odd" (the n=1
route) fails and path-following is needed.

But the STANDARD topological reason Tucker holds is a DEGREE argument: the antipodal
boundary map on S^1 has odd degree, and that degree is computed by an *oriented*
count of complementary edges, not a raw one. This script asks the concrete question
the next Lean session actually needs answered:

    Is there a natural ORIENTED complementary-edge count that IS invariantly odd
    across all 256 antipodal labellings of the hexagon?

If yes, THAT signed count -- not the raw count -- is the invariant a door-counting
Lean proof should track, and this pins it down without needing the full Freund-Todd
door-graph construction. Docker-free, exhaustive.

Model (identical to verify_tucker.py / SpernerTuckerHexagon.lean):
  boundary vertices v0..v5 (hexagon), centre c; antipodal v_{i+3} = -v_i;
  triangles T_i = (c, v_i, v_{i+1}); edges = 6 boundary + 6 spokes;
  labels in {+1,-1,+2,-2}; free: lam(v0),lam(v1),lam(v2),lam(c).
"""

from itertools import product
from collections import Counter


def boundary_edges():
    # oriented i -> i+1 around the hexagon
    return [(f"v{i}", f"v{(i + 1) % 6}") for i in range(6)]


def spokes():
    # oriented c -> v_i
    return [("c", f"v{i}") for i in range(6)]


def all_labelings():
    labels = [1, -1, 2, -2]
    for l0, l1, l2, lc in product(labels, repeat=4):
        yield {
            "v0": l0, "v1": l1, "v2": l2,
            "v3": -l0, "v4": -l1, "v5": -l2,  # boundary antipodal
            "c": lc,
        }


def is_comp(a, b):
    return a == -b


# --- candidate signed counts -------------------------------------------------

def raw_count(lam, edges):
    return sum(1 for (a, b) in edges if is_comp(lam[a], lam[b]))


def oriented_count(lam, edges):
    """Oriented edge (a,b): +1 if it is complementary with lam[a] > 0, -1 if
    complementary with lam[a] < 0. This is the signed incidence used in the
    mapping-degree computation."""
    s = 0
    for (a, b) in edges:
        if is_comp(lam[a], lam[b]):
            s += 1 if lam[a] > 0 else -1
    return s


def axis_count(lam, edges, k):
    """Raw count restricted to complementary edges of a FIXED axis {+k,-k}."""
    return sum(1 for (a, b) in edges
               if is_comp(lam[a], lam[b]) and abs(lam[a]) == k)


def axis_oriented_count(lam, edges, k):
    s = 0
    for (a, b) in edges:
        if is_comp(lam[a], lam[b]) and abs(lam[a]) == k:
            s += 1 if lam[a] > 0 else -1
    return s


def report(name, values):
    dist = dict(sorted(Counter(values).items()))
    odd = sum(1 for v in values if v % 2 != 0)
    always_odd = all(v % 2 != 0 for v in values)
    always_even = all(v % 2 == 0 for v in values)
    tag = "INVARIANTLY ODD" if always_odd else (
        "invariantly even" if always_even else "MIXED parity")
    print(f"[{name}] {tag}")
    print(f"    value distribution: {dist}")
    print(f"    odd fraction: {odd}/{len(values)}")
    return always_odd


if __name__ == "__main__":
    b_edges = boundary_edges()
    s_edges = spokes()
    all_edges = b_edges + s_edges

    lbls = list(all_labelings())
    print("=" * 72)
    print(f"Oriented complementary-count probe, hexagon n=2, {len(lbls)} antipodal labelings")
    print("=" * 72)

    winners = []

    # 1. raw over all edges (known: MIXED)
    report("raw count, all edges", [raw_count(l, all_edges) for l in lbls])
    print()

    # 2. oriented over all edges
    if report("ORIENTED count, all edges", [oriented_count(l, all_edges) for l in lbls]):
        winners.append("oriented count, all edges")
    print()

    # 3. oriented over boundary edges only (the S^1 degree)
    if report("ORIENTED count, boundary edges only",
              [oriented_count(l, b_edges) for l in lbls]):
        winners.append("oriented count, boundary edges only")
    print()

    # 4. oriented over spokes only
    if report("ORIENTED count, spokes only",
              [oriented_count(l, s_edges) for l in lbls]):
        winners.append("oriented count, spokes only")
    print()

    # 5/6. per-axis raw and oriented, all edges
    for k in (1, 2):
        report(f"raw count, axis {k}, all edges",
               [axis_count(l, all_edges, k) for l in lbls])
        if report(f"ORIENTED count, axis {k}, all edges",
                  [axis_oriented_count(l, all_edges, k) for l in lbls]):
            winners.append(f"oriented count, axis {k}, all edges")
        print()

    # 7/8. per-axis oriented on boundary only
    for k in (1, 2):
        if report(f"ORIENTED count, axis {k}, boundary only",
                  [axis_oriented_count(l, b_edges, k) for l in lbls]):
            winners.append(f"oriented count, axis {k}, boundary only")
        print()

    print("=" * 72)
    if winners:
        print("INVARIANTLY-ODD signed counts found:")
        for w in winners:
            print(f"  * {w}")
        print()
        print("=> The next Lean session should count THIS signed quantity mod 2,")
        print("   not the raw complementary-edge count.")
    else:
        print("No single-count parity invariant among the tested candidates.")
        print("=> confirms path-following (not a direct signed count) is required.")
