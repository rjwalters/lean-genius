#!/usr/bin/env python3
"""claude's third-implementation recount of the H3 triple-profile U-side census (review 2006).

From the ledger (Q7_H3_TRIPLE_MATCHING_CAPACITY_20260910.md): U = U0 ∪ U1 ∪ U2, |Ui| = 5, each block
induces a two-edge matching, each cross pair (Ui,Uj) induces a matching of size 5 (full case, all three)
or sizes (4,5,5) (partial case, one deficient pair). Every block's vertices share the special singleton
s_i, so two vertices of the same block may have NO common neighbour inside U; vertices of different blocks
may have at most one. Normalization: the two full cross matchings from block 0 are the identity
(relabel blocks 1, 2); the third cross matching is a permutation (full) or a partial permutation of
size 4 (partial, deficient pair = blocks 1,2). Orbits under the residual group: S5 on block 0
(propagated to blocks 1, 2 through the identity matchings) × block permutations preserving the
normalization (all 6 in the full case; identity and swap(1,2) in the partial case).
Usage: python3 u_census_recount.py {full|partial} [out.json]
"""
import itertools, collections, json, sys, time

MODE = sys.argv[1]
t0 = time.time()
B = [list(range(0, 5)), list(range(5, 10)), list(range(10, 15))]
def matchings5():
    out = []
    for a, b in itertools.combinations(range(5), 2):
        rest = [x for x in range(5) if x not in (a, b)]
        for c, d in itertools.combinations(rest, 2):
            if (a, b) < (c, d): out.append(((a, b), (c, d)))
    return out
M5 = matchings5(); assert len(M5) == 15

def cross_maps():
    if MODE == 'full':
        for p in itertools.permutations(range(5)):
            yield [(i, p[i]) for i in range(5)]
    else:
        for dom in itertools.combinations(range(5), 4):
            for img in itertools.permutations(range(5), 4):
                yield list(zip(dom, img))

def build(mA, mB, mC, bc):
    adj = [0] * 15
    def add(u, v): adj[u] |= 1 << v; adj[v] |= 1 << u
    for blk, m in zip(B, (mA, mB, mC)):
        for a, b in m: add(blk[a], blk[b])
    for i in range(5):
        add(B[0][i], B[1][i]); add(B[0][i], B[2][i])
    for i, j in bc: add(B[1][i], B[2][j])
    return adj

def ok(adj):
    blk = [v // 5 for v in range(15)]
    for a, b in itertools.combinations(range(15), 2):
        c = bin(adj[a] & adj[b]).count('1')
        if blk[a] == blk[b]:
            if c > 0: return False
        elif c > 1: return False
    return True

survivors = []
for mA in M5:
    for mB in M5:
        for mC in M5:
            for bc in cross_maps():
                adj = build(mA, mB, mC, bc)
                if ok(adj): survivors.append(tuple(adj))
n_lab = len(survivors)
print(f'{MODE}: normalized labelled survivors {n_lab} in {time.time()-t0:.0f}s', flush=True)

# Residual group: choose which old block becomes the new A (any of the three in the full case; only
# the old A in the partial case, since the new A must carry both perfect cross matchings), which of the
# remaining becomes new B, and a labelling sigma of the new A. The new B and C labels are then FORCED
# by the identity cross matchings: a vertex of new B/C takes the label of its unique neighbour in new A.
# This re-normalizes the image so every image lies in the normalized universe (a genuine transversal
# canonical form); a bare simultaneous relabelling after a block swap would leave the universe.
block_perms = list(itertools.permutations(range(3))) if MODE == 'full' else [(0, 1, 2), (0, 2, 1)]
SIGMAS = list(itertools.permutations(range(5)))
def images(adj):
    out = []
    for bp in block_perms:          # bp[k] = old block that becomes new block k
        oldA, oldB, oldC = bp
        for sigma in SIGMAS:
            m = [None] * 15
            for i in range(5):
                m[B[oldA][i]] = sigma[i]
            for newblk, oldblk in ((1, oldB), (2, oldC)):
                for y in B[oldblk]:
                    nb = [x for x in B[oldA] if (adj[y] >> x) & 1]
                    assert len(nb) == 1
                    m[y] = B[newblk][m[nb[0]]]
            out.append(relabel(adj, m))
    return out
def relabel(adj, m):
    new = [0] * 15
    for u in range(15):
        x = adj[u]; mu = m[u]
        while x:
            b = x & -x; v = b.bit_length() - 1; x ^= b
            new[mu] |= 1 << m[v]
    return tuple(new)
survset = set(survivors)
def canon(adj):
    ims = images(adj)
    assert all(im in survset for im in ims), 'image left the normalized universe'
    return min(ims)
reps = collections.Counter()
seen = set()
for adj in survivors:
    c = canon(adj)
    if c not in seen:
        seen.add(c)
orbits = len(seen)
result = {'mode': MODE, 'normalized_labelled_survivors': n_lab, 'residual_group_maps': len(block_perms)*len(SIGMAS),
          'orbits': orbits, 'seconds': round(time.time() - t0, 1),
          'scope': 'U-side census recount only (third implementation); no R-side, terminal or exclusion claim'}
print(json.dumps(result), flush=True)
if len(sys.argv) > 2: json.dump(result, open(sys.argv[2], 'w'), indent=1)
