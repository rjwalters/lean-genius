#!/usr/bin/env python3
"""Canonicalize the 1,294 stage-1 solutions under the residual symmetry
group (Sol msg 1899 spec: explicit generators, idempotence + orbit-
invariance tests).

Residual group acting on gauge-fixed solutions:
  - sigma in S4: comp relabeling (induces omitted-type permutation);
  - per-comp rotations r_e in {0,3,6,9}: tau_{o,e} += r_e (multiples of
    3 preserve the row-cover offset gauge c_e = 0);
  - global reflection: tau -> -tau (reflecting every comp and every
    orphan simultaneously keeps all slopes +1 and c_e = 0).
Global uniform rotations are absorbed by the per-orphan first-link
re-gauge; single-comp reflections break the slope normalization and are
NOT symmetries of the gauge-fixed model.
Group size (as generated words): 24 * 4^4 * 2 = 12,288.

Re-gauge after transform: per orphan subtract the first-link tau
(mod 12); canonical copy order = sorted tau-vectors within each type.
Canonical form of a solution = lex-min serialized transform over the
group.  Orbit census = distinct canonical forms.

Tests: (a) idempotence — canon(canon(s)) == canon(s);
       (b) orbit invariance — canon(g.s) == canon(s) for sampled g.
"""
import json, hashlib, sys, itertools
from itertools import permutations

PATH = (sys.argv[1] if len(sys.argv) > 1 else
        "/Volumes/Stripe/lean-genius/artifacts/erdos85-zerolayer/"
        "stage1_solutions.json")
doc = json.load(open(PATH))
sols_raw = doc["solutions"]
assert len(sols_raw) == 1294

COMPS = range(4)
def links(omit):
    return [e for e in COMPS if e != omit]

def parse(s):
    # -> dict omit -> list of 4 tau-dicts {comp: tau}
    out = {i: [dict() for _ in range(4)] for i in COMPS}
    for key, v in s.items():
        a, b, e = (int(x) for x in key.split(","))
        out[a][b][e] = v
    return out

def regauge(sol):
    # per orphan: subtract first-link tau; then sort copies per type
    out = {}
    for omit in COMPS:
        vecs = []
        for taus in sol[omit]:
            L = links(omit)
            base = taus[L[0]]
            vecs.append(tuple((taus[e] - base) % 12 for e in L))
        vecs.sort()
        out[omit] = vecs
    return out

def serialize(g):
    return json.dumps({str(k): g[k] for k in COMPS})

def transform(sol, sigma, rots, refl):
    # sigma: tuple new comp = sigma[old comp]; rots: per NEW comp add;
    # refl: negate taus first
    new = {i: [] for i in COMPS}
    for omit in COMPS:
        new_omit = sigma[omit]
        for taus in sol[omit]:
            nt = {}
            for e, t in taus.items():
                v = (-t) % 12 if refl else t
                ne = sigma[e]
                nt[ne] = (v + rots[ne]) % 12
            new[new_omit].append(nt)
    return new

GROUP = [(sigma, rots, refl)
         for sigma in permutations(range(4))
         for rots in itertools.product((0, 3, 6, 9), repeat=4)
         for refl in (False, True)]
assert len(GROUP) == 12288

def canon(sol):
    best = None
    for sigma, rots, refl in GROUP:
        cand = serialize(regauge(transform(sol, sigma, rots, refl)))
        if best is None or cand < best:
            best = cand
    return best

if __name__ == "__main__":
    parsed = [parse(s) for s in sols_raw]
    canons = [canon(p) for p in parsed]
    orbits = {}
    for c in canons:
        orbits[c] = orbits.get(c, 0) + 1
    print(f"orbits: {len(orbits)}  (from 1294 raw)")
    sizes = sorted(orbits.values(), reverse=True)
    print("orbit multiplicities (raw solutions per canonical form):",
          sizes[:20], "..." if len(sizes) > 20 else "")
    reps = sorted(orbits.keys())
    out = {"orbit_count": len(orbits),
           "generators": "S4 comp relabel; per-comp rot in {0,3,6,9}; "
                         "global reflection; group words 12288",
           "representatives": reps,
           "multiplicities": [orbits[r] for r in reps]}
    json.dump(out, open("stage1_orbits.json", "w"), indent=1)
    print("wrote stage1_orbits.json")
    # tests
    import random
    rng = random.Random(85)
    ok = True
    for i in rng.sample(range(1294), 6):
        c = canons[i]
        cp = parse({k: v for k, v in
                    zip((f"{o},{j},{e}" for o in COMPS for j in range(4)
                         for e in links(o)),
                        (t for o in COMPS
                         for vec in json.loads(c)[str(o)]
                         for t in vec))})
        ok &= canon(cp) == c        # idempotence
        g = GROUP[rng.randrange(len(GROUP))]
        ok &= canon(transform(parsed[i], *g)) == c   # orbit invariance
    print("tests:", "ALL OK" if ok else "FAIL")
