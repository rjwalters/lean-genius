#!/usr/bin/env python3
"""[12,4] branch (0,1): which defect classes admit an AFFINE q3 block?

Block o<->S, |o|=|S|=12, Q(o,S)=3: o-vertex v has S-neighbors
A_v = {u1*v+c1, u2*v+c2, u3*v+c3}, u_i in (Z12)* = {1,5,7,11} (affine phases).
Exact-coverage requirements:
  - |A_v| = 3 for all v (no degenerate phases)
  - every unordered S-pair with diff in allowed(d*) covered exactly once
  - pairs with diff outside allowed (defect class, mult-3, others) covered ZERO times
Enumerate all (u1,c1,u2,c2,u3,c3) up to phase reordering.

RESULT (2026-08-11): defect +-1 (the pinned case, squad 2606): ZERO affine
tilings -- so q3 phase-affineness closes [12,4] Branch2 (endpoint (A),
squad 2605/2607).  Counterfactual defects: +-2: 2 systems (pure-shift
{v,v+1,v+5}/{v,v+1,v+8}); +-4: 2 systems (mixed-multiplier); +-5: ZERO.
"""
from itertools import combinations, combinations_with_replacement, product

N = 12
UNITS = [1, 5, 7, 11]
ALL = {1, 2, 4, 5, 7, 8, 10, 11}

def run(defect):
    allowed = ALL - {defect % N, (-defect) % N}
    allowed_edges = set()
    for x in range(N):
        for d in allowed:
            allowed_edges.add(frozenset({x, (x + d) % N}))
    sols = []
    for (u1, u2, u3) in combinations_with_replacement(UNITS, 3):
        for (c1, c2, c3) in product(range(N), repeat=3):
            phases = [(u1, c1), (u2, c2), (u3, c3)]
            cover = {}
            ok = True
            for v in range(N):
                Av = [(u * v + c) % N for (u, c) in phases]
                if len(set(Av)) != 3:
                    ok = False
                    break
                for a, b in combinations(Av, 2):
                    e = frozenset({a, b})
                    cover[e] = cover.get(e, 0) + 1
                    if cover[e] > 1 or e not in allowed_edges:
                        ok = False
                        break
                if not ok:
                    break
            if ok and set(cover) == allowed_edges:
                sols.append(phases)
    # dedupe by the triple-system they generate
    systems = {}
    for ph in sols:
        sysm = frozenset(frozenset((u * v + c) % N for (u, c) in ph)
                         for v in range(N))
        systems.setdefault(sysm, []).append(ph)
    print(f"defect +-{defect}: affine solutions {len(sols)} "
          f"(distinct triple systems: {len(systems)})")
    for sysm, phs in list(systems.items())[:4]:
        print(f"   phases e.g. {phs[0]}  system sample {sorted(sorted(t) for t in sysm)[:3]}...")
    return len(systems)

if __name__ == "__main__":
    res = {d: run(d) for d in (1, 2, 4, 5)}
    print("\nSUMMARY (affine-realizable S-blocks by defect class):")
    for d, n in res.items():
        print(f"  defect +-{d}: {'AFFINE-FEASIBLE (' + str(n) + ' systems)' if n else 'AFFINE-INFEASIBLE'}")
