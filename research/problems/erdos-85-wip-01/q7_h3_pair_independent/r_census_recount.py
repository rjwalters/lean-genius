#!/usr/bin/env python3
"""claude's third-implementation recount of the H3 triple-profile secondary (R-side) census.

Written 2026-09-10 for review 2004, from the ledger constraints only
(Q7_H3_TRIPLE_SECONDARY_LEDGER_20260910.md, Q7_H3_TRIPLE_MATCHING_CAPACITY_20260910.md), before
reading sol-2's census.py: R = N(6) ∪ T(2), root u adjacent to all of N; C[N] a matching with
m in {1,2,3}; each T vertex has k_i in {0,1} N-neighbours and k_i + epsilon >= 1 where epsilon is the
T–T edge; r = e(R) in {3,4}; R ∪ {u} C4-free (every vertex pair has at most one common neighbour).
Orbits are taken under the full automorphism group of the fixed part, S6 (on N) × S2 (on T), by a
brute-force canonical form. Standard library only. Usage: python3 r_census_recount.py [out.json]
"""
import itertools, collections, json, sys, time

t0 = time.time()
N = list(range(6)); T = [6, 7]; U = 8
pairs = list(itertools.combinations(range(8), 2)); assert len(pairs) == 28

def c4free(edges):
    adj = {v: set() for v in range(9)}
    for a, b in edges: adj[a].add(b); adj[b].add(a)
    return all(len(adj[a] & adj[b]) <= 1 for a, b in itertools.combinations(range(9), 2))

surv = []; universe = 0
for r in (3, 4):
    for sub in itertools.combinations(pairs, r):
        universe += 1
        E = set(sub)
        m = sum(1 for a, b in E if a < 6 and b < 6)
        eps = int((6, 7) in E)
        k = [sum(1 for a, b in E if (a == t or b == t) and (a < 6 or b < 6)) for t in T]
        if not (1 <= m <= 3): continue
        if any(x > 1 for x in k): continue
        if any(x + eps < 1 for x in k): continue
        degN = collections.Counter()
        for a, b in E:
            if a < 6 and b < 6: degN[a] += 1; degN[b] += 1
        if any(v > 1 for v in degN.values()): continue
        if not c4free(list(E) + [(v, U) for v in N]): continue
        surv.append((frozenset(E), m, r))

def canon(E):
    best = None
    for p in itertools.permutations(range(6)):
        for q in ((6, 7), (7, 6)):
            mp = dict(zip(range(6), p)); mp[6] = q[0]; mp[7] = q[1]
            key = tuple(sorted(tuple(sorted((mp[a], mp[b]))) for a, b in E))
            if best is None or key < best: best = key
    return best

orb = collections.Counter(); reps = {}
for E, m, r in surv:
    c = canon(E)
    if c not in reps: reps[c] = (m, r); orb[(m, r)] += 1
result = {'scope': 'R-side census recount only (third implementation); no U-side or terminal claim',
          'universe_3_or_4_edge_subsets_of_28': universe, 'labelled_survivors': len(surv),
          'orbits': len(reps), 'orbits_by_m_r': {f'({m},{r})': n for (m, r), n in sorted(orb.items())},
          'orbit_representatives': [{'edges': [list(e) for e in c], 'm': mr[0], 'r': mr[1]} for c, mr in sorted(reps.items())],
          'seconds': round(time.time() - t0, 2)}
print(json.dumps({k: v for k, v in result.items() if k != 'orbit_representatives'}))
if len(sys.argv) > 1:
    json.dump(result, open(sys.argv[1], 'w'), indent=1)
