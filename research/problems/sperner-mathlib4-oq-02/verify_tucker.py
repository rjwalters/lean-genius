#!/usr/bin/env python3
"""
Brute-force verification of Tucker's lemma on small antipodally-symmetric
triangulations, and an empirical probe of the parity invariant that any
door-counting-style Lean proof would have to track.

Context (sperner-mathlib4-oq-02): the parent gallery proof
`proofs/Proofs/SpernerMathlib4.lean` proves Sperner's lemma via an abstract
`CellComplex` door-counting parity engine. The open question asks whether the
SAME engine yields Tucker's lemma (the antipodal analogue / combinatorial heart
of Borsuk-Ulam). This script does NOT need Docker or Lean -- it independently
checks the combinatorial statement we would formalize, on cases small enough to
enumerate exhaustively.

Tucker's lemma (combinatorial form): for an antipodally symmetric triangulation
T of the n-ball and a labelling lam: vertices -> {+-1,...,+-n} that is antipodal
on the boundary (lam(-v) = -lam(v)), some edge {u,w} of T is COMPLEMENTARY:
lam(u) = -lam(w).

Run: python3 verify_tucker.py
"""

from itertools import product

LABELS = None  # set per dimension: [+-1,...,+-n]


def is_complementary(a, b):
    """Edge labels a,b are complementary iff a = -b (i.e. {+k,-k})."""
    return a == -b


# ---------------------------------------------------------------------------
# Case n = 1 : B^1 = [-1, 1], symmetric triangulation with an odd number of
# interior vertices. Vertices indexed -m..m; antipodal map i |-> -i.
# Edges are consecutive pairs. Boundary = {-m, m}.
# ---------------------------------------------------------------------------
def verify_n1(m):
    """B^1 with vertices -m..m (2m+1 vertices), labels in {+1,-1}."""
    verts = list(range(-m, m + 1))
    edges = [(i, i + 1) for i in range(-m, m)]
    labels = [1, -1]
    free = [v for v in verts if v < 0] + [0]  # determine v<=0, mirror v>0
    total = 0
    bad = 0
    comp_counts = []
    for assign in product(labels, repeat=len(free)):
        lam = {}
        for v, val in zip(free, assign):
            lam[v] = val
        # antipodal on boundary: here whole structure is antipodal-symmetric,
        # but Tucker only REQUIRES antipodality on the boundary. We impose the
        # minimal hypothesis: only boundary vertices -m, m are constrained.
        lam[m] = -lam[-m]
        # interior positive vertices are FREE -> enumerate them too
        # (so re-do with all interior free). Handled by full enumeration below.
        total += 1
    # Full correct enumeration: free = boundary rep {-m} (mirror to m) + all
    # interior vertices -m+1..m-1 free.
    total = 0
    bad = 0
    comp_counts = []
    interior = list(range(-m + 1, m))
    for bval in labels:                      # lam[-m]; lam[m] = -bval
        for iv in product(labels, repeat=len(interior)):
            lam = {-m: bval, m: -bval}
            for v, val in zip(interior, iv):
                lam[v] = val
            c = sum(1 for (a, b) in edges if is_complementary(lam[a], lam[b]))
            comp_counts.append(c)
            total += 1
            if c == 0:
                bad += 1
    return total, bad, comp_counts


# ---------------------------------------------------------------------------
# Case n = 2 : B^2 disk, antipodally symmetric "hexagon + center"
# triangulation. Boundary vertices v0..v5 (hexagon), center c (interior).
# Antipodal map sigma: v_i |-> v_{(i+3)%6}, c |-> c.
# Triangles T_i = (c, v_i, v_{i+1}); edges = 6 boundary edges + 6 spokes.
# Labels in {+-1, +-2}. Boundary antipodal: lam(v_{i+3}) = -lam(v_i).
# Free choices: lam(v0),lam(v1),lam(v2),lam(c).
# ---------------------------------------------------------------------------
def verify_n2():
    labels = [1, -1, 2, -2]
    V = ["c"] + [f"v{i}" for i in range(6)]
    boundary_edges = [(f"v{i}", f"v{(i + 1) % 6}") for i in range(6)]
    spokes = [("c", f"v{i}") for i in range(6)]
    edges = boundary_edges + spokes

    total = 0
    bad = 0
    comp_counts = []
    examples_min = None
    for l0, l1, l2, lc in product(labels, repeat=4):
        lam = {
            "v0": l0, "v1": l1, "v2": l2,
            "v3": -l0, "v4": -l1, "v5": -l2,  # boundary antipodal
            "c": lc,
        }
        c = sum(1 for (a, b) in edges if is_complementary(lam[a], lam[b]))
        comp_counts.append(c)
        total += 1
        if c == 0:
            bad += 1
        if c >= 1 and (examples_min is None or c < examples_min[0]):
            examples_min = (c, dict(lam))
    return total, bad, comp_counts, examples_min


# ---------------------------------------------------------------------------
# Probe: does the parent's Sperner engine apply DIRECTLY?
# The parent concludes a PANCHROMATIC cell (coloring surjective onto Fin(d+1),
# i.e. d+1 distinct colors on a d-cell). Tucker concludes a COMPLEMENTARY EDGE.
# We check on n=2 whether "panchromatic triangle" and "complementary edge"
# coincide, to show they are genuinely different targets.
# ---------------------------------------------------------------------------
def probe_panchromatic_vs_complementary():
    labels = [1, -1, 2, -2]
    triangles = [("c", f"v{i}", f"v{(i + 1) % 6}") for i in range(6)]
    boundary_edges = [(f"v{i}", f"v{(i + 1) % 6}") for i in range(6)]
    spokes = [("c", f"v{i}") for i in range(6)]
    edges = boundary_edges + spokes

    has_comp_no_panchro = 0
    has_panchro_no_comp = 0
    for l0, l1, l2, lc in product(labels, repeat=4):
        lam = {"v0": l0, "v1": l1, "v2": l2,
               "v3": -l0, "v4": -l1, "v5": -l2, "c": lc}
        comp = any(is_complementary(lam[a], lam[b]) for (a, b) in edges)
        # "panchromatic" in the 3-color sense is ill-typed for 4 signed labels;
        # use the natural antipodal analogue: a triangle is "rainbow-signed" if
        # its 3 vertex labels are pairwise non-complementary AND use >=2 axes.
        panchro = any(
            len({abs(lam[a]), abs(lam[b]), abs(lam[cc])}) == 2
            and not any(is_complementary(lam[x], lam[y])
                        for x, y in [(a, b), (b, cc), (a, cc)])
            for (a, b, cc) in triangles)
        if comp and not panchro:
            has_comp_no_panchro += 1
        if panchro and not comp:
            has_panchro_no_comp += 1
    return has_comp_no_panchro, has_panchro_no_comp


def summarize(name, total, bad, counts):
    from collections import Counter
    dist = dict(sorted(Counter(counts).items()))
    odd = sum(1 for c in counts if c % 2 == 1)
    print(f"[{name}] labelings={total}  no-complementary-edge={bad}  "
          f"(Tucker holds iff this is 0)")
    print(f"    complementary-edge-count distribution: {dist}")
    print(f"    labelings with ODD complementary-edge count: {odd}/{total}")


if __name__ == "__main__":
    print("=" * 70)
    print("Tucker's lemma -- exhaustive verification on small triangulations")
    print("=" * 70)

    for m in (1, 2, 3):
        t, b, cc = verify_n1(m)
        summarize(f"n=1, B^1 with {2*m+1} vertices", t, b, cc)
    print()

    t, b, cc, ex = verify_n2()
    summarize("n=2, B^2 hexagon+center (6 triangles)", t, b, cc)
    print(f"    min complementary-edge example (count={ex[0]}): {ex[1]}")
    print()

    hcnp, hpnc = probe_panchromatic_vs_complementary()
    print("[engine-divergence probe] n=2 hexagon")
    print(f"    labelings with complementary edge but NO rainbow-signed "
          f"triangle: {hcnp}")
    print(f"    labelings with rainbow-signed triangle but NO complementary "
          f"edge: {hpnc}")
    print("    (nonzero on either side => the Sperner 'panchromatic cell'")
    print("     target and the Tucker 'complementary edge' target are NOT")
    print("     interchangeable; the parent engine's conclusion is the wrong")
    print("     shape for Tucker.)")

    print()
    print("RESULT: assertions below must all pass.")
    # Tucker holds on every enumerated case:
    for m in (1, 2, 3):
        t, b, cc = verify_n1(m)
        assert b == 0, f"n=1 m={m}: found labeling with no complementary edge!"
    t, b, cc, ex = verify_n2()
    assert b == 0, "n=2: found labeling with no complementary edge!"
    print("OK: every antipodal labeling on every test triangulation has a "
          "complementary edge (Tucker confirmed).")
