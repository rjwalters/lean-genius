#!/usr/bin/env python3
"""A/B worker for the defect-ledger clause family (no-closure derivation,
msg-1164 plan / msg-1225 mandate).

Usage: ab_worker.py <table_json> <outdir> <arm>
  arm = base   : identical encoding to remote_worker.py (fair re-baseline)
        v1     : + F1 symmetric miss pinning
                 + F2 per-vertex paired-direction fan equalities
                 + F3a paired-product common totals (=22)
        v2     : v1 + F3b unpaired-product common totals (constants from m)

Sound augmentations only: every added clause is a theorem of the base
axioms (m-symmetry msg 535; fan-landing injectivity = C4-freeness; product
walk censuses from the defect-ledger derivation 2026-08-08).
Writes <outdir>/<tag>.<arm>.{cnf,verdict[,drat.gz]}.
"""
import itertools, sys, time, json, hashlib, os, subprocess
from pysat.solvers import Glucose42
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool, CNF

table_json, outdir, arm = sys.argv[1], sys.argv[2], sys.argv[3]
assert arm in ("base", "v1", "v2")
mtab = {tuple(map(int, k.strip("()").split(","))): v
        for k, v in json.loads(table_json).items()}
tag = hashlib.sha1(json.dumps(sorted(mtab.items())).encode()).hexdigest()[:16]
os.makedirs(outdir, exist_ok=True)

def m_of(a, b):
    return mtab.get((min(a, b), max(a, b)), 0)

N = 40
blocks = [list(range(5 * i, 5 * i + 5)) for i in range(8)]
blk = [i // 5 for i in range(N)]
paired = lambda b: b ^ 1
pool = IDPool()
def ev(i, j):
    a, b = min(i, j), max(i, j)
    return pool.id(('e', a, b))
cl = []
# ---- base encoding (verbatim from remote_worker.py) ----
for b in range(8):
    base = 5 * b
    med = [(base, base + 1), (base + 2, base + 3)]
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
    matched.update({5 * b, 5 * b + 1, 5 * b + 2, 5 * b + 3})
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
    for j in range(8):
        if j <= c or j == paired(c): continue
        want = m_of(c, j)
        lits = [missvar(x, j) for x in blocks[c] if x in matched]
        if want > 0:
            cnf = CardEnc.equals(lits=lits, bound=want, vpool=pool,
                                 encoding=EncType.seqcounter)
            cl.extend(cnf.clauses)
        else:
            for l in lits: cl.append([-l])
for c in range(8):
    base = 5 * c
    fars = [j for j in range(8) if j not in (c, paired(c))]
    def leq(x, y):
        for j in fars:
            for k in fars:
                if j > k: cl.append([-missvar(x, j), -missvar(y, k)])
    leq(base, base + 1)
    leq(base + 2, base + 3)
    for j in fars:
        for k in fars:
            if j > k: cl.append([-missvar(base, j), -missvar(base + 2, k)])

# ---- ledger augmentations ----
if arm in ("v1", "v2"):
    # F1: symmetric miss pinning (m-symmetry is a theorem; the base encoder
    # pins only the c<j direction).
    for c in range(8):
        for j in range(8):
            if j >= c or j == paired(c): continue   # the missing direction
            want = m_of(c, j)
            lits = [missvar(x, j) for x in blocks[c] if x in matched]
            if want > 0:
                cnf = CardEnc.equals(lits=lits, bound=want, vpool=pool,
                                     encoding=EncType.seqcounter)
                cl.extend(cnf.clauses)
            else:
                for l in lits: cl.append([-l])

    # Common indicators for the 4 paired products.
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

    # F2: per-vertex fan equality into the paired block:
    #   sum_z C(x,z) + sum_{w matched middle} s(x,w) = degfar(x)
    # where s(x,w) = e(x,w) AND missvar(w, paired(blk(x))).
    def svar(x, w):
        return pool.id(('s', x, w))
    for x in range(N):
        cp = paired(blk[x])
        slits = []
        for w in range(N):
            if w not in matched: continue
            if blk[w] in (blk[x], cp): continue
            s = svar(x, w)
            cl.append([-s, ev(x, w)])
            cl.append([-s, missvar(w, cp)])
            cl.append([s, -ev(x, w), -missvar(w, cp)])
            slits.append(s)
        clits = [cvar(x, z) for z in blocks[cp]]
        cnf = CardEnc.equals(lits=clits + slits, bound=degfar(x),
                             vpool=pool, encoding=EncType.seqcounter)
        cl.extend(cnf.clauses)

    # F3a: paired-product common totals: exactly 22 of 25 (defect ledger).
    for k in range(4):
        bi, bj = 2 * k, 2 * k + 1
        clits = [cvar(x, z) for x in blocks[bi] for z in blocks[bj]]
        cnf = CardEnc.equals(lits=clits, bound=22, vpool=pool,
                             encoding=EncType.seqcounter)
        cl.extend(cnf.clauses)

if arm == "v2":
    # F3b: unpaired-product common totals = 20 + m(a,pair(b)) + m(b,pair(a)).
    def tvar2(x, w, z):
        a, b = min(x, z), max(x, z)
        return pool.id(('t', a, w, b))
    def cvar2(x, z):
        a, b = min(x, z), max(x, z)
        return pool.id(('c', a, b))
    for a, b in itertools.combinations(range(8), 2):
        if b == paired(a): continue
        midblocks = [c for c in range(8)
                     if c not in (a, b, paired(a), paired(b))]
        mids = [w for w in range(N) if blk[w] in midblocks]
        clits = []
        for x in blocks[a]:
            for z in blocks[b]:
                ors = []
                for w in mids:
                    t = tvar2(x, w, z)
                    cl.append([-t, ev(x, w)])
                    cl.append([-t, ev(w, z)])
                    cl.append([t, -ev(x, w), -ev(w, z)])
                    ors.append(t)
                # partner apexes: in-block edges are fixed true, so the
                # 2-walk through a partner reduces to a single edge literal.
                if x in matched:
                    px = x + 1 if x % 5 in (0, 2) else x - 1
                    ors.append(ev(px, z))
                if z in matched:
                    pz = z + 1 if z % 5 in (0, 2) else z - 1
                    ors.append(ev(x, pz))
                C = cvar2(x, z)
                cl.append([-C] + ors)
                for o in ors: cl.append([-o, C])
                clits.append(C)
        want = 20 + m_of(a, paired(b)) + m_of(b, paired(a))
        cnf = CardEnc.equals(lits=clits, bound=want, vpool=pool,
                             encoding=EncType.seqcounter)
        cl.extend(cnf.clauses)

print(f"[{tag}.{arm}] {len(cl)} clauses, {pool.top} vars", flush=True)
CNF(from_clauses=cl).to_file(f"{outdir}/{tag}.{arm}.cnf")
s = Glucose42(bootstrap_with=cl, with_proof=True)
t0 = time.time(); res = s.solve(); dt = time.time() - t0
verdict = "SAT" if res else "UNSAT"
ver = "N/A"
if not res:
    pf = s.get_proof()
    open(f"{outdir}/{tag}.{arm}.drat", "w").write("\n".join(pf) + "\n")
    r = subprocess.run(["drat-trim", f"{outdir}/{tag}.{arm}.cnf",
                        f"{outdir}/{tag}.{arm}.drat",
                        "-c", f"{outdir}/{tag}.{arm}.core.cnf"],
                       capture_output=True, text=True)
    ver = "VERIFIED" if "s VERIFIED" in r.stdout else "NOT-VERIFIED"
    if ver == "VERIFIED":
        subprocess.run(["gzip", "-f", f"{outdir}/{tag}.{arm}.drat"])
else:
    model = set(l for l in s.get_model() if l > 0)
    edges = [(i, j) for i, j in itertools.combinations(range(N), 2)
             if ev(i, j) in model]
    open(f"{outdir}/{tag}.{arm}.model", "w").write(repr(edges))
open(f"{outdir}/{tag}.{arm}.verdict", "w").write(
    f"{tag} {arm} {verdict} {dt:.1f}s drat:{ver}\n")
print(f"{tag} {arm} {verdict} {dt:.1f}s {ver}", flush=True)
