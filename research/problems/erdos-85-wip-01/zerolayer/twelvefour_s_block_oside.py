#!/usr/bin/env python3
"""o-side labeling obstructions for [12,4] branch (0,1), defect +-1.

The 4 set-level triangle decompositions of Cay(Z12,{+-2,+-4,+-5}) assign
12 triples to the 12 vertices of the orphan o (an order-12 cyclic component
with its own D-adjacency +-1).  o-pairs at D-adjacency have ZERO commons
(squad 2606), so consecutive o-vertices must carry DISJOINT triples: the
system must admit a Hamiltonian cycle in the disjointness graph of its 12
triples.

RESULT (2026-08-11): all four systems admit such labelings (disjointness
graphs are 5-regular with Hamiltonian cycles) -- D-adjacency disjointness
alone does NOT kill the non-circulant systems.  Adding distance-2
disjointness kills all four, but no framework law justifies distance-2
(the literal-cycle reading is refuted by S's own ledger: +-2 is in S's
REQUIRED coverage set).  See squad 2605/2607; the lawful closure path is
q3 phase-affineness + twelvefour_s_block_affine.py's ZERO result.
"""
from itertools import combinations

N = 12
ALL = {2, 4, 5, 7, 8, 10}  # +-2,+-4,+-5

def decomps():
    edges = set()
    for x in range(N):
        for d in ALL:
            edges.add(frozenset({x, (x + d) % N}))
    tris = [frozenset(t) for t in combinations(range(N), 3)
            if all((a - b) % N in ALL or (b - a) % N in ALL
                   for a, b in combinations(t, 2))]
    tri_edges = {t: frozenset(frozenset(p) for p in combinations(sorted(t), 2))
                 for t in tris}
    edge_list = sorted(edges, key=sorted)
    by_edge = {e: [t for t in tris if e in tri_edges[t]] for e in edge_list}
    sols, used, chosen = [], set(), []

    def bt():
        rem = [e for e in edge_list if e not in used]
        if not rem:
            sols.append(list(chosen))
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
    return sols

def ham_cycle_exists(tris, dist2=False):
    n = len(tris)
    disj = [[len(tris[i] & tris[j]) == 0 and i != j for j in range(n)]
            for i in range(n)]
    path = [0]
    seen = {0}

    def ok_ext(nxt):
        if not disj[path[-1]][nxt]:
            return False
        if dist2 and len(path) >= 2 and not disj[path[-2]][nxt]:
            return False
        return True

    def bt():
        if len(path) == n:
            if not disj[path[-1]][path[0]]:
                return False
            if dist2 and (not disj[path[-2]][path[0]] or not disj[path[-1]][path[1]]):
                return False
            return True
        for nxt in range(1, n):
            if nxt not in seen and ok_ext(nxt):
                seen.add(nxt)
                path.append(nxt)
                if bt():
                    return True
                path.pop()
                seen.remove(nxt)
        return False

    return bt(), path

if __name__ == "__main__":
    systems = decomps()
    print(f"set-level decompositions (defect +-1, allowed +-2,+-4,+-5): {len(systems)}")
    for i, sol in enumerate(systems):
        ok1, p1 = ham_cycle_exists(sol)
        ok2, _ = ham_cycle_exists(sol, dist2=True)
        deg = sorted(sum(1 for j, t2 in enumerate(sol)
                         if j != k and not (t & t2))
                     for k, t in enumerate(sol))
        print(f"system {i}: disjointness degrees {deg}")
        print(f"   dist-1 Hamiltonian labeling: "
              f"{'EXISTS ' + str([sorted(sol[p]) for p in p1]) if ok1 else 'NONE'}")
        print(f"   dist-1+2 labeling: {'EXISTS' if ok2 else 'NONE (unjustified law)'}")
