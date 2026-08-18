#!/usr/bin/env python3
"""Independent validator for the durable stage-1 solutions artifact
(Sol msg 1908 spec).

Usage: validate_stage1_solutions.py [path-to-json]
Default path: /Volumes/Stripe/lean-genius/artifacts/erdos85-zerolayer/
stage1_solutions.json

Checks, with NO CP-SAT dependency (pure python re-validation):
  1. sha256 of the file equals the recorded
     05f2d5d613b283ea81aabb318cf283bc6a2f22257c13d8344d249a3b8b575f5d
  2. exactly 1294 records, all distinct
  3. every record satisfies the stage-1 constraint system:
     - 16 orphans (omit 0..3, copy 0..3), taus on the 3 links, in 0..11
     - gauge: first-link (lowest comp index) tau == 0
     - row offsets tau mod 3 pairwise distinct across the 3 links
     - copy-ordering: tau of the second link nondecreasing in copy
     - pair injectivity: for every pair of distinct orphans and every
       two shared comps e,f: (tau2_e - tau1_e) != (tau2_f - tau1_f) mod 12
"""
import sys, json, hashlib
from itertools import combinations

EXPECTED_SHA = ("05f2d5d613b283ea81aabb318cf283bc6a2f22257c1"
                "3d8344d249a3b8b575f5d")
PATH = (sys.argv[1] if len(sys.argv) > 1 else
        "/Volumes/Stripe/lean-genius/artifacts/erdos85-zerolayer/"
        "stage1_solutions.json")

data = open(PATH, "rb").read()
h = hashlib.sha256(data).hexdigest()
assert h == EXPECTED_SHA, f"HASH MISMATCH: {h}"
print("hash OK")

doc = json.loads(data)
sols = doc["solutions"]
assert doc["count"] == 1294 and len(sols) == 1294, len(sols)
canon = {json.dumps(s, sort_keys=True) for s in sols}
assert len(canon) == 1294, "duplicate records"
print("count 1294, all distinct OK")

COMPS = range(4)
ORPHANS = [(i, j) for i in COMPS for j in range(4)]
def links(o):
    return [e for e in COMPS if e != o[0]]

bad = 0
for s in sols:
    tau = {}
    for key, v in s.items():
        a, b, e = (int(x) for x in key.split(","))
        tau[(a, b), e] = v
    ok = True
    for o in ORPHANS:
        L = links(o)
        ts = [tau[o, e] for e in L]
        if not all(0 <= t <= 11 for t in ts): ok = False
        if tau[o, L[0]] != 0: ok = False
        if len({t % 3 for t in ts}) != 3: ok = False
    for i in COMPS:
        for j in range(3):
            L = links((i, j))
            if tau[(i, j), L[1]] > tau[(i, j + 1), L[1]]: ok = False
    for o1, o2 in combinations(ORPHANS, 2):
        shared = [e for e in links(o1) if e in links(o2)]
        for e, f in combinations(shared, 2):
            d = ((tau[o2, e] - tau[o1, e]) - (tau[o2, f] - tau[o1, f])) % 12
            if d == 0: ok = False
    if not ok: bad += 1
print(f"constraint validation: {1294 - bad}/1294 pass")
assert bad == 0, f"{bad} invalid records"
print("ALL OK")
