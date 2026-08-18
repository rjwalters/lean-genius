#!/usr/bin/env python3
"""[12,4] S-side (e4 = Z12) coverage design search -- scout grade.

Setup (corrected census 60f630022b + forced quotient matrix; squad 2601):
  S = Z12.  Per-vertex out-budget 16 = 1 (c0) + 3 (used: Q(S,L)=3) + 12 orphans.
  Orphan budget 12 = 9 (three B36, Q(S,B_i)=3 each) + 3 (D-side).
  D-side census: nD4 + 3*nD12 = 3  =>  (nD4,nD12) in {(3,0),(0,1)}.

S-pair common-neighbor sources:
  c0 (cover Z12->Z3, kernel {0,3,6,9}): covers offsets {3,6,9} exactly once. FORCED.
  L (Q(L,S)=1) and B36 (Q(B,S)=1): reverse-unit => ZERO S-pair commons.
  intra-S: a[S][S]=0 forced (a[L][S]=0 would force a[S][S]=3, killed by
  degree_sixteen_orderTwelve_diagonalQuotient_ne_three).
  D4 (cover Z12->Z4, kernel {0,4,8}): covers offsets {4,8} exactly once per atom.
  D12 (q3 block, |o|=12, Q(o,S)=3): each o-vertex is a triple A_v in Z12.

Branch (3,0): three D4 atoms each cover +-4 pairs => >=2 commons => C4. DEAD
  (graph-facing: false_of_degree_sixteen_orderTwelve_three_orderFour_unit_targets,
  200e8085f5, via false_of_two_unit_componentQuotients_lcm_ncard_lt).
Branch (0,1): D-adjacency is BY DEFINITION coordinate +-1 (squad 2606), so the
  defect class d* = +-1 and required offsets are {+-2,+-4,+-5}.  The block must
  exactly cover them: exact triangle decomposition of Cay(Z12, {+-2,+-4,+-5})
  (36 edges, 12 triangles); mult-3 diffs forbidden inside triples (double
  coverage vs c0 => C4), +-1 diffs forbidden (D-adjacent pairs have 0 commons).

This script also decides the counterfactual defect classes {+-2,+-4,+-5} for
red-team completeness.  RESULT (2026-08-11): d*=+-1: FOUR set-level systems,
all non-circulant -- these are the countermodels showing the single-3-set
endpoint no_three_residualDifferenceSet_zmod_twelve (77fecb5740) does NOT
close Branch2 alone (squad 2605/2607).  Companion scripts:
twelvefour_s_block_affine.py (affine-phase enumeration: ZERO tilings ->
endpoint (A)), twelvefour_s_block_oside.py (o-side labeling obstructions).
"""
from itertools import combinations
import sys

N = 12
ALL = {1, 2, 4, 5, 7, 8, 10, 11}  # +-1,+-2,+-4,+-5 as residues

def norm(d):
    return d % N

def run(defect):
    allowed = ALL - {defect % N, (-defect) % N}
    # edges of Cayley graph
    edges = set()
    for x in range(N):
        for d in allowed:
            e = frozenset({x, (x + d) % N})
            if len(e) == 2:
                edges.add(e)
    assert len(edges) == 36, (defect, len(edges))
    # all triangles: triples with all three pairwise diffs allowed
    tris = []
    for t in combinations(range(N), 3):
        ok = True
        for a, b in combinations(t, 2):
            if norm(a - b) not in allowed and norm(b - a) not in allowed:
                ok = False
                break
        if ok:
            tris.append(frozenset(t))
    # exact cover: partition edges into triangles
    edge_list = sorted(edges, key=sorted)
    tri_edges = {t: frozenset(frozenset(p) for p in combinations(sorted(t), 2))
                 for t in tris}
    by_edge = {e: [t for t in tris if e in tri_edges[t]] for e in edge_list}
    solutions = []
    used = set()
    chosen = []

    def bt():
        if len(solutions) >= 5:
            return
        rem = [e for e in edge_list if e not in used]
        if not rem:
            solutions.append(list(chosen))
            return
        e = min(rem, key=lambda e: sum(1 for t in by_edge[e]
                                       if not (tri_edges[t] & used)))
        for t in by_edge[e]:
            te = tri_edges[t]
            if te & used:
                continue
            used.update(te)
            chosen.append(t)
            bt()
            chosen.pop()
            used.difference_update(te)

    bt()
    print(f"defect +-{defect}: allowed diffs {sorted(allowed)}  "
          f"triangles available: {len(tris)}  "
          f"decompositions found (cap 5): {len(solutions)}")
    for sol in solutions[:4]:
        shifted = {frozenset((x + 1) % N for x in t) for t in sol}
        circ = shifted == set(map(frozenset, sol))
        print(f"   {sorted(sorted(t) for t in sol)}  circulant(shift1)={circ}")
    return len(solutions)

if __name__ == "__main__":
    total = {}
    for d in (1, 2, 4, 5):
        total[d] = run(d)
    print("\nSUMMARY (branch (0,1) S-block set-level feasibility by defect class):")
    for d, n in total.items():
        print(f"  defect +-{d}: {'FEASIBLE (' + str(n) + ' systems)' if n else 'INFEASIBLE'}")
