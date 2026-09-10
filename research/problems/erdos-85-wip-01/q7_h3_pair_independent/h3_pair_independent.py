#!/usr/bin/env python3
"""Independent re-implementation of the H3 pair-profile exclusion (claude, 2026-09-10).

Written from the paper reductions in Q7_H3_PAIR_B{0,1}_CORE_REDUCTION_20260910.md and
Q7_H3_SUPPORT_EDGE_LEDGER_20260910.md only; no code or normalization is shared with
the sol-1 verifiers. Search order deliberately differs: empties are assigned triples
one empty at a time in strictly increasing triple order (the sol verifiers branch on
singleton demands). Cores are enumerated WITHOUT the sol normalization: every perfect
matching consistent with BC=J is generated and pruned by C4 checks, then reduced to
orbit representatives under the exact symmetry group (color permutations fixing the
pair-edge structure x ordinary relabelings) by brute-force canonical form.

Object: simple C4-free graph on 49 vertices, min degree 7, exactly 3 vertices of
degree 8 (highs, independent), and the pair support profile: 25 empty, 18 singleton,
3 pair-support low vertices. b = number of edges among the 3 pair vertices (0 or 1).

Facts used (all re-derived by hand from the length-two count, see room 46138):
  BB^T = 7I + J, BC = J, C1 = 7 - t, Ct = 3.
  Each high H_i has neighbours: the two pair vertices P_a (a != i) and six colour-i
  singletons; N(H_i) induces a perfect matching.
  A singleton s of colour i needs, for each colour j, exactly one low neighbour
  adjacent to H_j; a P-neighbour of s supplies that for every j it is adjacent to.
Usage: python3 h3_pair_independent.py {0|1} [--cores-only]
"""
import sys, itertools, json, time, collections

B = int(sys.argv[1])
CORES_ONLY = '--cores-only' in sys.argv
OUT = f'/private/tmp/claude-501/-Users-rwalters-GitHub-lean-genius/9d4660cc-e007-48ed-8318-5b8f8816b95f/scratchpad/h3pair/result_b{B}.json'

# ---------- vertex layout ----------
H = [0, 1, 2]                 # highs
P = [3, 4, 5]                 # P[a] misses colour a (adjacent to H_b, H_c, b,c != a)
def S(i, k): return 6 + 6 * i + k   # singleton k (0..5) of colour i
SING = [S(i, k) for i in range(3) for k in range(6)]
COLOR = {S(i, k): i for i in range(3) for k in range(6)}
NCORE = 24
NE = 25                       # empties
N = NCORE + NE
EMP = list(range(NCORE, N))

def bits(m):
    while m:
        b = m & -m
        yield b.bit_length() - 1
        m ^= b

class G:
    __slots__ = ('adj', 'deg')
    def __init__(self):
        self.adj = [0] * N
        self.deg = [0] * N
    def copy(self):
        g = G(); g.adj = self.adj[:]; g.deg = self.deg[:]; return g
    def has(self, u, v): return (self.adj[u] >> v) & 1
    def add(self, u, v):
        self.adj[u] |= 1 << v; self.adj[v] |= 1 << u; self.deg[u] += 1; self.deg[v] += 1
    def rem(self, u, v):
        self.adj[u] &= ~(1 << v); self.adj[v] &= ~(1 << u); self.deg[u] -= 1; self.deg[v] -= 1
    def c4_free_edge(self, u, v):
        """Adding u-v (nonadjacent) closes a C4 iff some w in N(u), x in N(v) with w~x."""
        d2 = 0
        for w in bits(self.adj[u]):
            d2 |= self.adj[w]
        return not (d2 & self.adj[v])
    def common(self, u, v): return bin(self.adj[u] & self.adj[v]).count('1')
    def check_all_pairs(self, verts):
        for a, b in itertools.combinations(verts, 2):
            if self.common(a, b) > 1: return False
        return True

# ---------- fixed part of the core (forced by BB^T=7I+J, BC=J) ----------
base = G()
for a in P:
    for i in H:
        if i != P.index(a):
            base.add(a, i)
for i in H:
    for k in range(6):
        base.add(S(i, k), i)
pp_edges = [] if B == 0 else [(P[0], P[1])]
for u, v in pp_edges:
    base.add(u, v)

# Which colours does P_a already cover through highs or P-neighbours? For BC=J at P_a:
# colour j is covered iff some LOW neighbour of P_a is adjacent to H_j. Highs are not low.
def p_low_covers(g, a):
    cov = set()
    for w in bits(g.adj[a]):
        if w in P:
            for j in H:
                if g.has(w, j): cov.add(j)
    return cov
# P_a needs one singleton of each uncovered colour. Assign special singletons WLOG:
# colour-j singletons are interchangeable before any other structure, so the special
# of colour j attached to P_a is chosen as the lowest unused index of colour j.
special = {}   # singleton -> P it is attached to
next_idx = {i: 0 for i in H}
for a in P:
    need = [j for j in H if j not in p_low_covers(base, a)]
    for j in need:
        s = S(j, next_idx[j]); next_idx[j] += 1
        base.add(a, s); special[s] = a
ordinary = [s for s in SING if s not in special]
ORD_SET = set(ordinary)
ORD_BY_COLOR = {i: [s for s in ordinary if COLOR[s] == i] for i in H}
# sanity: degrees so far
assert all(base.deg[a] == 2 + len(pp_edges and [e for e in pp_edges if a in e]) + len([s for s in special if special[s] == a]) for a in P)

# For each singleton, which colours j still need a singleton neighbour of colour j?
def needs(g, s):
    out = []
    for j in H:
        covered = False
        for w in bits(g.adj[s]):
            if w in P and g.has(w, j): covered = True
        if not covered: out.append(j)
    return out
NEEDS = {s: needs(base, s) for s in SING}
# Demand of empties per singleton: degree 7 minus (high + P-neighbours + singleton needs)
EMPTY_DEMAND = {s: 7 - 1 - sum(1 for w in bits(base.adj[s]) if w in P) - len(NEEDS[s]) for s in SING}
# P_a's empties and the colour they must host
P_EMPTY = {a: 7 - base.deg[a] for a in P}
P_HOST_COLOR = {a: [j for j in H if j not in p_low_covers(base, a) and j != P.index(a) or j == P.index(a)][0] for a in P}
# (P_a misses exactly colour a; its empties need a colour-a singleton.)  Verify directly:
for a in P:
    miss = [j for j in H if not base.has(a, j)]
    assert miss == [P.index(a)]
    P_HOST_COLOR[a] = P.index(a)

# ---------- stage 1: enumerate all cores ----------
# Required matchings: for each unordered colour pair {i,j} (i<j) a perfect matching between
# A_ij = {s of colour i : j in NEEDS[s]} and A_ji; for i=j a perfect matching inside A_ii.
pairs_needed = {}
for i in H:
    for j in H:
        if i <= j:
            Aij = [s for s in SING if COLOR[s] == i and j in NEEDS[s]]
            Aji = [s for s in SING if COLOR[s] == j and i in NEEDS[s]]
            pairs_needed[(i, j)] = (Aij, Aji)
            if i == j: assert Aij == Aji and len(Aij) % 2 == 0
            else: assert len(Aij) == len(Aji), (i, j, Aij, Aji)

# Build the list of "slots": each singleton s and colour j in NEEDS[s] must get exactly one edge.
cores = []
nodes1 = 0
def stage1(g, slots_left):
    global nodes1
    nodes1 += 1
    if not slots_left:
        cores.append(g.adj[:NCORE])
        return
    s, j = slots_left[0]
    rest = slots_left[1:]
    touched = {i: [u for u in ORD_BY_COLOR[i] if g.adj[u] != base.adj[u]] for i in H}
    for t in SING:
        if COLOR[t] != j or t == s: continue
        if COLOR[s] not in NEEDS[t]: continue
        if g.has(s, t): continue
        # first-touch normalization: an untouched ordinary must be the lowest untouched of its colour
        if t in ORD_SET and t not in touched[COLOR[t]]:
            lowest = next(u for u in ORD_BY_COLOR[COLOR[t]] if u not in touched[COLOR[t]] and u != s)
            if t != lowest: continue
        # t must still have its colour-COLOR[s] slot open
        if any(g.has(t, u) and COLOR[u] == COLOR[s] for u in bits(g.adj[t]) if u in COLOR): continue
        if not g.c4_free_edge(s, t): continue
        g.add(s, t)
        # the reciprocal slot (t, COLOR[s]) is now filled: drop it
        new_rest = [x for x in rest if x != (t, COLOR[s])]
        stage1(g, new_rest)
        g.rem(s, t)

slots = [(s, j) for s in SING for j in NEEDS[s]]
t0 = time.time()
stage1(base.copy(), slots)
# every core must have every singleton at core degree 1 + #P + #needs, and all-pairs C4-free
def core_ok(adj):
    g = G(); g.adj = adj + [0] * NE
    for s in SING:
        if bin(adj[s]).count('1') != 1 + sum(1 for w in bits(adj[s]) if w in P) + len(NEEDS[s]): return False
    return g.check_all_pairs(range(NCORE))
cores = [c for c in cores if core_ok(c)]
print(f'b={B}: stage1 nodes {nodes1}, C4-free labelled cores {len(cores)} in {time.time()-t0:.1f}s', flush=True)

# ---------- symmetry reduction to orbit representatives ----------
# Group: colour permutations that preserve the P-P edge set (all of S3 for b=0; the
# transposition (0 1) and identity for b=1), combined with permutations of the ordinary
# singletons within each colour. Specials are relabelled consistently with the colour map.
def color_perms():
    for perm in itertools.permutations(H):
        img = {tuple(sorted((P[perm[P.index(u)]], P[perm[P.index(v)]]))) for u, v in pp_edges}
        if img == {tuple(sorted(e)) for e in pp_edges}: yield perm
SPEC_BY_COLOR_P = {(COLOR[s], special[s]): s for s in special}
FIXED_MASK = sum(1 << v for v in range(NCORE) if v not in ORD_SET)
def base_maps():
    for perm in color_perms():
        m = {}
        for i in H: m[i] = perm[i]
        for a in P: m[a] = P[perm[P.index(a)]]
        for s, a in special.items():
            m[s] = SPEC_BY_COLOR_P[(perm[COLOR[s]], P[perm[P.index(a)]])]
        for i in H:
            src = ORD_BY_COLOR[i]; dst = ORD_BY_COLOR[perm[i]]
            assert len(src) == len(dst)
            for u, v in zip(src, dst): m[u] = v
        yield m
BASE_MAPS = list(base_maps())
def relabel(adj, m):
    new = [0] * NCORE
    for u in range(NCORE):
        mu = m[u]
        for v in bits(adj[u]):
            new[mu] |= 1 << m[v]
    return new
def canon(adj):
    """Canonical form under colour perms x ordinary relabelings, by invariant refinement
    (adjacency to the fixed vertices) plus brute force inside equal-invariant cells."""
    best = None
    for m0 in BASE_MAPS:
        a1 = relabel(adj, m0)
        cell_perms = []
        for i in H:
            ords = ORD_BY_COLOR[i]
            inv = {u: (a1[u] & FIXED_MASK, bin(a1[u]).count('1')) for u in ords}
            order = sorted(ords, key=lambda u: inv[u])
            # split into cells of equal invariant
            cells = []
            for u in order:
                if cells and inv[cells[-1][0]] == inv[u]: cells[-1].append(u)
                else: cells.append([u])
            # all ways to order within cells; target slots are ords in index order
            def cell_orders(cells=cells):
                for combo in itertools.product(*[itertools.permutations(c) for c in cells]):
                    yield [u for c in combo for u in c]
            cell_perms.append(list(cell_orders()))
        for combo in itertools.product(*cell_perms):
            m = {v: v for v in range(NCORE)}
            for i, order in zip(H, combo):
                for u, slot in zip(order, ORD_BY_COLOR[i]): m[u] = slot
            key = tuple(relabel(a1, m))
            if best is None or key < best: best = key
    return best
MAPS = BASE_MAPS
reps = {}
for c in cores:
    k = canon(c)
    reps.setdefault(k, c)
print(f'b={B}: colour perms {len(MAPS)}, first-touch cores {len(cores)}, orbit representatives {len(reps)}', flush=True)
if CORES_ONLY:
    sys.exit(0)

# ---------- stage 2/3 per representative ----------
stats = collections.Counter()
completed_graphs = []
def hosts_eligible(g, a):
    col = P_HOST_COLOR[a]
    return [s for s in SING if COLOR[s] == col and EMPTY_DEMAND[s] > 0 and g.common(a, s) == 0]

def run_case(core_adj, case_id):
    g = G(); g.adj = list(core_adj) + [0] * NE
    g.deg = [bin(x).count('1') for x in g.adj]
    demand = dict(EMPTY_DEMAND)
    empties = list(EMP)
    e_ptr = [0]
    # stage 2a: P-adjacent empties with hosts (unordered distinct host subsets per P_a)
    p_cases = []
    def assign_hosts(ai, g, demand, chosen):
        if ai == len(P):
            p_cases.append(True)
            run_triples(g, demand, chosen)
            return
        a = P[ai]
        k = P_EMPTY[a]
        elig = hosts_eligible(g, a)
        elig = [s for s in elig if demand[s] > 0]
        for subset in itertools.combinations(elig, k):
            es = []
            ok = True
            for s in subset:
                e = empties[e_ptr[0]]; e_ptr[0] += 1; es.append((e, s))
                if not (g.c4_free_edge(e, a) and True): ok = False
                g.add(e, a)
                if not g.c4_free_edge(e, s): ok = False
                g.add(e, s); demand[s] -= 1
            if ok:
                assign_hosts(ai + 1, g, demand, chosen + [(e, a, s) for (e, s) in es])
            for e, s in reversed(es):
                g.rem(e, s); demand[s] += 1; g.rem(e, a); e_ptr[0] -= 1
    # stage 2b: remaining empties each take a transversal triple. Exact-cover style:
    # branch on the singleton with the fewest eligible triples, choose exactly demand[s]
    # pairwise pair-disjoint triples for it (each becomes a new empty vertex).
    def run_triples(g, demand, chosen):
        n_free = NE - sum(P_EMPTY.values())
        cand = []
        for s0 in [s for s in SING if COLOR[s] == 0]:
            for s1 in [s for s in SING if COLOR[s] == 1]:
                if g.common(s0, s1): continue
                for s2 in [s for s in SING if COLOR[s] == 2]:
                    if g.common(s0, s2) or g.common(s1, s2): continue
                    cand.append((s0, s1, s2))
        stats['triple_candidates'] += len(cand)
        by_s = {s: [t for t in cand if s in t] for s in SING}
        used_pairs = set()
        first_free = e_ptr[0]
        def eligible(t):
            return all(demand[x] > 0 for x in t) and not ({(t[0], t[1]), (t[0], t[2]), (t[1], t[2])} & used_pairs)
        def rec(k, g, demand):
            nonlocal used_pairs
            stats['incidence_nodes'] += 1
            if k == n_free:
                if all(d == 0 for d in demand.values()):
                    stats['incidence_leaves'] += 1
                    run_empty_edges(g)
                return
            # most constrained singleton
            best = None; best_opts = None
            for s in SING:
                d = demand[s]
                if d == 0: continue
                opts = [t for t in by_s[s] if eligible(t)]
                if len(opts) < d: return
                if best is None or len(opts) < len(best_opts): best, best_opts = s, opts
            s = best; d = demand[s]
            for subset in itertools.combinations(best_opts, d):
                prs = set()
                ok = True
                for t in subset:
                    p3 = {(t[0], t[1]), (t[0], t[2]), (t[1], t[2])}
                    if p3 & prs: ok = False; break
                    prs |= p3
                if not ok: continue
                if any(demand[x] < sum(1 for t in subset if x in t) for x in SING): continue
                added = []
                for idx, t in enumerate(subset):
                    e = empties[first_free + k + idx]
                    for x in t:
                        if not g.c4_free_edge(e, x): ok = False; break
                        g.add(e, x); demand[x] -= 1; added.append((e, x))
                    if not ok: break
                if ok:
                    used_pairs |= prs
                    rec(k + len(subset), g, demand)
                    used_pairs -= prs
                for e, x in reversed(added):
                    g.rem(e, x); demand[x] += 1
        rec(0, g, demand)
    # stage 3: empty-empty edges
    def run_empty_edges(g):
        stats['empty_edge_roots'] += 1
        # every non-empty vertex must now have its final degree
        for v in range(NCORE):
            want = 8 if v in H else 7
            assert g.deg[v] == want, (v, g.deg[v], want)
        assert g.check_all_pairs(range(N))
        resid = {e: 7 - g.deg[e] for e in EMP}
        def rec(g, resid):
            stats['empty_edge_nodes'] += 1
            active = [e for e in EMP if resid[e] > 0]
            if not active:
                stats['COMPLETED_GRAPHS'] += 1
                completed_graphs.append([g.adj[v] for v in range(N)])
                return
            # pick the active vertex with fewest admissible partners
            best = None; best_adm = None
            for u in active:
                adm = [v for v in active if v != u and not g.has(u, v) and g.c4_free_edge(u, v)]
                if len(adm) < resid[u]:
                    return
                if best is None or len(adm) < len(best_adm):
                    best, best_adm = u, adm
            u = best
            for subset in itertools.combinations(best_adm, resid[u]):
                ok = True; added = []
                for v in subset:
                    if resid[v] == 0 or not g.c4_free_edge(u, v): ok = False; break
                    g.add(u, v); added.append(v); resid[u] -= 1; resid[v] -= 1
                if ok:
                    rec(g, resid)
                for v in reversed(added):
                    g.rem(u, v); resid[u] += 1; resid[v] += 1
        rec(g, resid)
    assign_hosts(0, g, demand, [])
    return len(p_cases)

t1 = time.time()
total_cases = 0
for ci, (k, c) in enumerate(sorted(reps.items())):
    n = run_case(c, ci)
    total_cases += n
    print(f'  rep {ci+1}/{len(reps)}: host cases {n}, cumulative stats {dict(stats)}, {time.time()-t1:.0f}s', flush=True)
result = {'b': B, 'labelled_cores': len(cores), 'orbit_reps': len(reps), 'group_size': len(MAPS),
          'host_cases': total_cases, 'stats': dict(stats), 'completed_graphs': len(completed_graphs),
          'seconds': time.time() - t0}
json.dump(result, open(OUT, 'w'), indent=1)
print('RESULT', json.dumps(result), flush=True)
