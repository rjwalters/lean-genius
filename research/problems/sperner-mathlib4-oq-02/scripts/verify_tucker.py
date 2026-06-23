#!/usr/bin/env python3
"""
ORIENT verification for sperner-mathlib4-oq-02 (Tucker's lemma).

Tucker's lemma: for an antipodally-symmetric triangulation of B^n with a labelling
λ: V → {±1,...,±n} that is antipodal on the boundary (λ(-v) = -λ(v) for v ∈ ∂B^n),
some edge {u,v} is COMPLEMENTARY: λ(u) = -λ(v).

We verify by EXHAUSTIVE search over all admissible labellings that no labelling
avoids a complementary edge, on two concrete antipodally-symmetric triangulations:
  n = 1 : interval [-1,1] with 2m+1 vertices (antipodal endpoints).
  n = 2 : hexagonal disk (6 boundary vertices in 3 antipodal pairs) + center.
"""
from itertools import product

def has_complementary_edge(lab, edges):
    return any(lab[u] == -lab[v] for (u,v) in edges)

# ---------- n = 1 : path -m..m, boundary = {-m, m}, antipodal ----------
def verify_n1(m):
    verts = list(range(-m, m+1))            # 2m+1 vertices on the segment
    edges = [(i, i+1) for i in range(-m, m)]
    labels = [1, -1]                        # {±1}
    interior = [v for v in verts if v not in (-m, m)]
    total = checked = 0
    # boundary antipodal: λ(m) = -λ(-m). choose λ(-m) freely.
    for lneg in labels:
        lpos = -lneg
        for interior_vals in product(labels, repeat=len(interior)):
            lab = {-m: lneg, m: lpos}
            for v, val in zip(interior, interior_vals):
                lab[v] = val
            total += 1
            if has_complementary_edge(lab, edges):
                checked += 1
    return total, checked

# ---------- n = 2 : hexagon v0..v5 (v_{i+3} = -v_i) + center c ----------
def verify_n2():
    # boundary vertices 0..5, center = 6. antipodal pairing i <-> i+3.
    hex_edges = [(i, (i+1)%6) for i in range(6)]      # boundary cycle
    spokes    = [(6, i) for i in range(6)]            # center to each boundary
    edges = hex_edges + spokes
    labels = [1, -1, 2, -2]                           # {±1, ±2}
    total = good = 0
    bad_examples = []
    # antipodal on boundary: λ(i+3) = -λ(i). choose λ(0),λ(1),λ(2) freely; center free.
    for l0, l1, l2, lc in product(labels, repeat=4):
        lab = {0:l0, 1:l1, 2:l2, 3:-l0, 4:-l1, 5:-l2, 6:lc}
        total += 1
        if has_complementary_edge(lab, edges):
            good += 1
        else:
            bad_examples.append(dict(lab))
    return total, good, bad_examples

ok = True
for m in (1, 2, 3, 5):
    tot, chk = verify_n1(m)
    status = "OK" if chk == tot else "FAIL"
    if chk != tot: ok = False
    print(f"n=1, segment 2m+1={2*m+1} verts: {chk}/{tot} labellings have a complementary edge  [{status}]")

tot, good, bad = verify_n2()
status = "OK" if good == tot else f"FAIL ({len(bad)} counterexamples)"
if good != tot: ok = False
print(f"n=2, hexagon+center (7 verts): {good}/{tot} labellings have a complementary edge  [{status}]")
if bad:
    print("  first counterexample labelling:", bad[0])

print()
print("ALL CHECKS PASSED — no admissible labelling avoids a complementary edge" if ok
      else "FAILURES ABOVE (model too coarse or edge set wrong — investigate)")
