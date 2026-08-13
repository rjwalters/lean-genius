#!/usr/bin/env python3
"""Family-level CNF generator for the h=1 profile wholesale scout.

This is the exact generator used for the family lanes.  `pure` contains only
the certified base structure and paired-product ledger; `aug` additionally
contains the certified witness, k-sum, and A/B pointwise cap laws.
"""
import itertools, sys
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool, CNF

profile, variant, outpath = sys.argv[1], sys.argv[2], sys.argv[3]
assert profile in ("AAAA", "AAAB", "AABB", "ABBB", "BBBB")
assert variant in ("pure", "aug")

IN = []
for kind in profile:
    IN.extend((1, 2) if kind == "A" else (2, 2))

N = 40
blocks = [list(range(5 * i, 5 * i + 5)) for i in range(8)]
blk = [i // 5 for i in range(N)]
paired = lambda b: b ^ 1
pool = IDPool()
def ev(i, j):
    a, b = min(i, j), max(i, j)
    return pool.id(('e', a, b))
cl = []
for b in range(8):
    base = 5 * b
    med = [(base, base + 1)] + ([(base + 2, base + 3)] if IN[b] == 2 else [])
    for a, c in itertools.combinations(blocks[b], 2):
        cl.append([ev(a, c)] if (a, c) in med else [-ev(a, c)])
for b in range(0, 8, 2):
    for i in blocks[b]:
        for j in blocks[b + 1]:
            cl.append([-ev(i, j)])
for i, j in itertools.combinations(range(N), 2):
    others = [w for w in range(N) if w != i and w != j]
    if blk[i] == blk[j]:
        for w in others:
            cl.append([-ev(i, w), -ev(j, w)])
    else:
        for w, w2 in itertools.combinations(others, 2):
            cl.append([-ev(i, w), -ev(j, w), -ev(i, w2), -ev(j, w2)])
for b in range(8):
    for y in range(N):
        if blk[y] == paired(b): continue
        lits = [ev(y, x) for x in blocks[b] if x != y]
        for l1, l2 in itertools.combinations(lits, 2):
            cl.append([-l1, -l2])
matched = set()
for b in range(8):
    matched.update({5 * b, 5 * b + 1})
    if IN[b] == 2:
        matched.update({5 * b + 2, 5 * b + 3})
def degfar(y):
    return 5 if y in matched else 6
for y in range(N):
    fars = [ev(y, x) for x in range(N)
            if x != y and blk[x] not in (blk[y], paired(blk[y]))]
    cnf = CardEnc.equals(lits=fars, bound=degfar(y),
                         vpool=pool, encoding=EncType.seqcounter)
    cl.extend(cnf.clauses)
def missvar(w, b):
    return pool.id(('x', w, b))
for w in range(N):
    if w not in matched: continue
    for b in range(8):
        if b in (blk[w], paired(blk[w])): continue
        xv = missvar(w, b)
        lits = [ev(w, z) for z in blocks[b]]
        for l in lits: cl.append([-xv, -l])
        cl.append([xv] + lits)
for c in range(8):
    base = 5 * c
    fars = [j for j in range(8) if j not in (c, paired(c))]
    def leq(x, y):
        for j in fars:
            for k in fars:
                if j > k: cl.append([-missvar(x, j), -missvar(y, k)])
    leq(base, base + 1)
    if IN[c] == 2:
        leq(base + 2, base + 3)
        for j in fars:
            for k in fars:
                if j > k: cl.append([-missvar(base, j), -missvar(base + 2, k)])
def tvar(x, w, z):
    a, b = min(x, z), max(x, z)
    return pool.id(('t', a, w, b))
def cvar(x, z):
    a, b = min(x, z), max(x, z)
    return pool.id(('c', a, b))
for k in range(4):
    bi, bj = 2 * k, 2 * k + 1
    mids = [w for w in range(N) if blk[w] not in (bi, bj)]
    for x in blocks[bi]:
        for z in blocks[bj]:
            ts = []
            for w in mids:
                t = tvar(x, w, z)
                cl.append([-t, ev(x, w)])
                cl.append([-t, ev(w, z)])
                cl.append([t, -ev(x, w), -ev(w, z)])
                ts.append(t)
            C = cvar(x, z)
            cl.append([-C] + ts)
            for t in ts: cl.append([-t, C])
    clits = [cvar(x, z) for x in blocks[bi] for z in blocks[bj]]
    bound = 30 - 2 * IN[bi] - 2 * IN[bj]
    cnf = CardEnc.equals(lits=clits, bound=bound, vpool=pool,
                         encoding=EncType.seqcounter)
    cl.extend(cnf.clauses)

if variant == "aug":
    def kvar(x, w):
        return pool.id(('k', x, w))
    for a in range(8):
        am = paired(a)
        all_kv = []
        for x in blocks[a]:
            kvs = []
            for w in range(N):
                if w not in matched: continue
                if blk[w] in (a, am): continue
                kv = kvar(x, w)
                cl.append([-kv, ev(x, w)])
                cl.append([-kv, missvar(w, am)])
                cl.append([kv, -ev(x, w), -missvar(w, am)])
                kvs.append(kv)
            all_kv.extend(kvs)
            if x not in matched:
                cl.append(list(kvs))
            in_A_pair = profile[a // 2] == "A"
            kmax = (2 if x not in matched else 1) if in_A_pair else \
                   (4 if x not in matched else 3)
            cnf = CardEnc.atmost(lits=kvs, bound=kmax, vpool=pool,
                                 encoding=EncType.seqcounter)
            cl.extend(cnf.clauses)
        cnf = CardEnc.equals(lits=all_kv, bound=2 * IN[am], vpool=pool,
                             encoding=EncType.seqcounter)
        cl.extend(cnf.clauses)

CNF(from_clauses=cl).to_file(outpath)
print(f"{profile} {variant}: {len(cl)} clauses -> {outpath}", flush=True)
