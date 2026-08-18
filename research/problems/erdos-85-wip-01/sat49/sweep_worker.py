#!/usr/bin/env python3
"""Sweep worker with time budget + cube-and-conquer fallback (mandate item 2).

Usage: sweep_worker.py <table_json> <outdir> [arm] [budget_s]
  arm      : base | v1 | v2   (ledger clause family arms; default base)
  budget_s : monolithic solve budget in seconds (default 900). On interrupt,
             the instance is split into 25 cubes by branching on the two
             unmatched-vertex edges u(B0)->B2 and u(B1)->B3 (each exactly-one
             over 5 choices, so the cubes PARTITION the space), each cube
             added as unit clauses and solved to completion with its own
             DRAT + drat-trim verification.

Verdict file records MONO or CUBE mode, per-cube times, and the combined
verdict (UNSAT iff all cubes UNSAT; any SAT cube -> SAT with model).
"""
import itertools, sys, time, json, hashlib, os, subprocess
from threading import Timer
from pysat.solvers import Glucose42
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool, CNF

table_json, outdir = sys.argv[1], sys.argv[2]
arm = sys.argv[3] if len(sys.argv) > 3 else "base"
budget = float(sys.argv[4]) if len(sys.argv) > 4 else 900.0
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

if arm in ("v1", "v2"):
    for c in range(8):
        for j in range(8):
            if j >= c or j == paired(c): continue
            want = m_of(c, j)
            lits = [missvar(x, j) for x in blocks[c] if x in matched]
            if want > 0:
                cnf = CardEnc.equals(lits=lits, bound=want, vpool=pool,
                                     encoding=EncType.seqcounter)
                cl.extend(cnf.clauses)
            else:
                for l in lits: cl.append([-l])
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
    for k in range(4):
        bi, bj = 2 * k, 2 * k + 1
        clits = [cvar(x, z) for x in blocks[bi] for z in blocks[bj]]
        cnf = CardEnc.equals(lits=clits, bound=22, vpool=pool,
                             encoding=EncType.seqcounter)
        cl.extend(cnf.clauses)
if arm == "v2":
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

# ---- solve: monolithic with budget, cube on interrupt ----
def run_drat(cnf_path, drat_path):
    r = subprocess.run(["drat-trim", cnf_path, drat_path, "-c",
                        cnf_path.replace(".cnf", ".core.cnf")],
                       capture_output=True, text=True)
    ok = "s VERIFIED" in r.stdout
    if ok:
        subprocess.run(["gzip", "-f", drat_path])
    return "VERIFIED" if ok else "NOT-VERIFIED"

t0 = time.time()
s = Glucose42(bootstrap_with=cl, with_proof=True)
timer = Timer(budget, s.interrupt)
timer.start()
res = s.solve_limited(expect_interrupt=True)
timer.cancel()
dt = time.time() - t0

if res is not None:
    verdict = "SAT" if res else "UNSAT"
    ver = "N/A"
    if not res:
        base_cnf = f"{outdir}/{tag}.{arm}.cnf"
        CNF(from_clauses=cl).to_file(base_cnf)
        open(f"{outdir}/{tag}.{arm}.drat", "w").write(
            "\n".join(s.get_proof()) + "\n")
        ver = run_drat(base_cnf, f"{outdir}/{tag}.{arm}.drat")
    else:
        model = set(l for l in s.get_model() if l > 0)
        edges = [(i, j) for i, j in itertools.combinations(range(N), 2)
                 if ev(i, j) in model]
        open(f"{outdir}/{tag}.{arm}.model", "w").write(repr(edges))
    open(f"{outdir}/{tag}.{arm}.verdict", "w").write(
        f"{tag} {verdict} {dt:.1f}s drat:{ver} mode:MONO arm:{arm} "
        f"table:{json.dumps(sorted(mtab.items()))}\n")
    print(f"{tag} {arm} {verdict} {dt:.1f}s {ver} MONO", flush=True)
    sys.exit(0)

# Budget exhausted: cube and conquer. Branch on the unmatched vertex of B0
# (vertex 4) -> its unique neighbor in B2, and unmatched of B1 (vertex 9)
# -> unique neighbor in B3. Exactly-one holds for both (unmatched vertices
# cover every unpaired branch), so the 25 cubes partition the search space.
s.delete()
print(f"{tag} {arm} BUDGET({budget:.0f}s) -> cubing 25", flush=True)
u0, u1 = 4, 9
cubes = [[ev(u0, a), ev(u1, b)] for a in blocks[2] for b in blocks[3]]
cube_dir = f"{outdir}/cubes-{tag}.{arm}"
os.makedirs(cube_dir, exist_ok=True)
alltimes, verdict, sat_model, all_ver = [], "UNSAT", None, "VERIFIED"
for ci, cube in enumerate(cubes):
    ccl = cl + [[l] for l in cube]
    cs = Glucose42(bootstrap_with=ccl, with_proof=True)
    ct0 = time.time()
    cres = cs.solve()
    cdt = time.time() - ct0
    alltimes.append(round(cdt, 1))
    if cres:
        verdict = "SAT"
        model = set(l for l in cs.get_model() if l > 0)
        sat_model = [(i, j) for i, j in itertools.combinations(range(N), 2)
                     if ev(i, j) in model]
        cs.delete()
        break
    ccnf = f"{cube_dir}/c{ci}.cnf"
    CNF(from_clauses=ccl).to_file(ccnf)
    open(f"{cube_dir}/c{ci}.drat", "w").write("\n".join(cs.get_proof()) + "\n")
    cver = run_drat(ccnf, f"{cube_dir}/c{ci}.drat")
    if cver != "VERIFIED":
        all_ver = "NOT-VERIFIED"
    cs.delete()
tdt = time.time() - t0
if verdict == "SAT" and sat_model is not None:
    open(f"{outdir}/{tag}.{arm}.model", "w").write(repr(sat_model))
    all_ver = "N/A"
open(f"{outdir}/{tag}.{arm}.verdict", "w").write(
    f"{tag} {verdict} {tdt:.1f}s drat:{all_ver} mode:CUBE25 arm:{arm} "
    f"cubetimes:{alltimes} table:{json.dumps(sorted(mtab.items()))}\n")
print(f"{tag} {arm} {verdict} {tdt:.1f}s {all_ver} CUBE25 {alltimes}",
      flush=True)
