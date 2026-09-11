#!/usr/bin/env python3
"""claude's independent audit of a q9 semiregular CNF instance (board #39, editor 50462 'audit').

Given a generator output directory (graph.cnf + map.json), this script
  1. checks the CNF sha against map.json and (optionally) a ledger sha;
  2. re-derives the orbit decomposition of unordered vertex pairs under t -> t+1 on residues, and checks
     that map.json's orbit list is exactly that decomposition (every pair once, right block/shift);
  3. recovers every Tseitin AND gate from the CNF (z <-> a & b, z > |a|,|b|) and checks that every
     non-primary variable has exactly one defining gate, so the extension of a primary assignment is unique;
  4. evaluates the whole CNF under many primary assignments and compares with an independent graph oracle
     (build the 80-vertex graph from the true orbits; min degree >= d and no pair with two common neighbours):
     random assignments at several densities, greedy random C4-free invariant graphs (which exercise the degree
     threshold at the boundary), and single-orbit mutations of those.
Usage: python3 encoding_audit.py DIR [--ledger-sha SHA] [--samples N] [--seed S]
"""
import argparse, hashlib, itertools, json, random, sys, time
import numpy as np

ap = argparse.ArgumentParser()
ap.add_argument('dir'); ap.add_argument('--ledger-sha', default=None)
ap.add_argument('--samples', type=int, default=400); ap.add_argument('--seed', type=int, default=1)
a = ap.parse_args()
rng = random.Random(a.seed)
meta = json.load(open(a.dir + '/map.json'))
n, m, d = meta['n'], meta['m'], meta['minimum_degree']
cnf_bytes = open(a.dir + '/graph.cnf', 'rb').read()
sha = hashlib.sha256(cnf_bytes).hexdigest()
report = {'dir': a.dir, 'n': n, 'm': m, 'd': d, 'cnf_sha256': sha,
          'sha_matches_map': sha == meta.get('cnf_sha256'),
          'sha_matches_ledger': (sha == a.ledger_sha) if a.ledger_sha else None}

# ---- 1/2. orbit decomposition, re-derived
k = n // m
assert n % m == 0
def orbit_of(u, v):
    a_, b_ = u // m, v // m
    if a_ > b_ or (a_ == b_ and u % m > v % m): u, v = v, u; a_, b_ = b_, a_
    s = (v % m - u % m) % m
    if a_ == b_:
        s = min(s, (-s) % m)
    return (a_, b_, s)
my_orbits = {}
for u, v in itertools.combinations(range(n), 2):
    my_orbits.setdefault(orbit_of(u, v), set()).add((u, v))
their = {}
for o in meta['orbits']:
    key = (o['blocks'][0], o['blocks'][1], o['shift'])
    assert key not in their
    their[key] = {tuple(e) for e in o['edges']}
report['orbit_count'] = len(their)
report['orbits_match_rederivation'] = (their == my_orbits)
primaries = sorted(o['var'] for o in meta['orbits'])
assert len(set(primaries)) == len(primaries)
var_edges = {o['var']: [tuple(e) for e in o['edges']] for o in meta['orbits']}

# ---- 3. parse CNF, recover gates
lines = cnf_bytes.decode().split('\n')
hdr = lines[0].split(); assert hdr[:2] == ['p', 'cnf']
nvars, ncl = int(hdr[2]), int(hdr[3])
clauses = []
for ln in lines[1:]:
    if not ln.strip(): continue
    t = [int(x) for x in ln.split()]
    assert t[-1] == 0 and 0 not in t[:-1]
    clauses.append(tuple(t[:-1]))
assert len(clauses) == ncl, (len(clauses), ncl)
report['nvars'] = nvars; report['nclauses'] = ncl
cls_set = set(tuple(sorted(c)) for c in clauses)
gates = {}
prim_set = set(primaries)
for c in clauses:
    if len(c) == 3:
        for z in c:
            others = [x for x in c if x != z]
            if z > 0 and z not in prim_set and z != 1 and z > max(abs(x) for x in others):
                a1, b1 = -others[0], -others[1]
                if tuple(sorted((-z, a1))) in cls_set and tuple(sorted((-z, b1))) in cls_set:
                    assert z not in gates or gates[z] == (a1, b1), ('two gates define', z)
                    gates[z] = (a1, b1)
non_primary = [v for v in range(2, nvars + 1) if v not in set(primaries)]
report['gate_count'] = len(gates)
report['every_nonprimary_has_gate'] = all(v in gates for v in non_primary)
report['gates_topologically_ordered'] = all(abs(x) < z for z, (x, y) in gates.items() for x in (x, y))
gate_order = sorted(gates)
# clause arrays for vectorised evaluation
maxlen = max(len(c) for c in clauses)
CL = np.zeros((ncl, maxlen), dtype=np.int64)
for i, c in enumerate(clauses): CL[i, :len(c)] = c

def extend(assign):
    val = np.zeros(nvars + 1, dtype=bool); val[1] = True
    for v in primaries: val[v] = assign[v]
    for z in gate_order:
        x, y = gates[z]
        vx = val[abs(x)] ^ (x < 0); vy = val[abs(y)] ^ (y < 0)
        val[z] = vx and vy
    return val
def cnf_sat(val):
    lit_true = np.where(CL > 0, val[np.abs(CL)], np.where(CL < 0, ~val[np.abs(CL)], False))
    return bool(lit_true.any(axis=1).all())
def oracle(assign):
    adj = [set() for _ in range(n)]
    for v in primaries:
        if assign[v]:
            for u, w in var_edges[v]: adj[u].add(w); adj[w].add(u)
    if min(len(x) for x in adj) < d: return False, 'degree'
    for u in range(n):
        for v in range(u + 1, n):
            if len(adj[u] & adj[v]) > 1: return False, 'C4'
    return True, 'ok'

# ---- 4. test assignments
tests = []
# classify non-gate clauses into families: 'degree' = unit clauses whose literal is an OR-gate output
# (AND of two negated inputs), 'c4' = the AMO clauses (unit forced-false AND-of-edges, binary (-seen,-x)).
gate_clauses = set()
for z, (x, y) in gates.items():
    gate_clauses.add(tuple(sorted((-z, x)))); gate_clauses.add(tuple(sorted((-z, y)))); gate_clauses.add(tuple(sorted((z, -x, -y))))
fam = {}
for i, c in enumerate(clauses):
    key = tuple(sorted(c))
    if key in gate_clauses or c == (1,): continue
    if len(c) == 1:
        z = abs(c[0])
        if z in gates:
            x, y = gates[z]
            # AMO forced-false conjunction = AND of two positive edge variables; anything else is a degree output
            fam[i] = 'c4' if (x > 0 and y > 0 and x in prim_set and y in prim_set and c[0] < 0) else 'degree'
        else:
            assert z in set(primaries) and c[0] < 0, ('unclassified unit clause', c, z in gates)
            fam[i] = 'c4'
    else:
        fam[i] = 'c4'
report['degree_output_clauses'] = sum(1 for v in fam.values() if v == 'degree')
report['c4_clauses'] = sum(1 for v in fam.values() if v == 'c4')
report['degree_outputs_equal_block_count'] = (report['degree_output_clauses'] == k)
fam_idx = {f: np.array([i for i, v in fam.items() if v == f], dtype=np.int64) for f in ('degree', 'c4')}
def families_failing(val):
    lit_true = np.where(CL > 0, val[np.abs(CL)], np.where(CL < 0, ~val[np.abs(CL)], False))
    ok = lit_true.any(axis=1)
    return {f for f, idx in fam_idx.items() if not ok[idx].all()}
def oracle2(assign):
    adj = [set() for _ in range(n)]
    for v in primaries:
        if assign[v]:
            for u, w in var_edges[v]: adj[u].add(w); adj[w].add(u)
    fails = set()
    if min(len(x) for x in adj) < d: fails.add('degree')
    if any(len(adj[u] & adj[v]) > 1 for u in range(n) for v in range(u + 1, n)): fails.add('c4')
    return fails
def run(assign, tag):
    exp = oracle2(assign); val = extend(assign); got = families_failing(val)
    full = cnf_sat(val)
    tests.append((tag, exp, got, full))
    if exp != got or full != (not exp): print('MISMATCH', tag, exp, got, full, file=sys.stderr)
t0 = time.time()
ap2 = a
for p in (0.3, 0.4, 0.5):
    for _ in range(max(5, a.samples // 10)):
        run({v: rng.random() < p for v in primaries}, f'dense p={p} (degree positive)')
import os
if os.path.exists(a.dir + '/solver.log') or os.path.exists(a.dir + '/model.log'):
    pth = a.dir + ('/solver.log' if os.path.exists(a.dir + '/solver.log') else '/model.log')
    lits = set()
    for line in open(pth):
        if line.startswith('v '): lits.update(int(t) for t in line.split()[1:] if int(t) != 0)
    if lits: run({v: (v in lits) for v in primaries}, 'solver witness model')
for p in (0.03, 0.06, 0.1, 0.15, 0.25):
    for _ in range(a.samples // 5):
        run({v: rng.random() < p for v in primaries}, f'random p={p}')
# greedy C4-free invariant graphs: shuffle orbits, add while C4-free; then check the degree boundary
def c4free_graph(assign):
    adj = [set() for _ in range(n)]
    for v in primaries:
        if assign[v]:
            for u, w in var_edges[v]: adj[u].add(w); adj[w].add(u)
    return all(len(adj[u] & adj[v]) <= 1 for u in range(n) for v in range(u + 1, n)), adj
greedy = []
for _ in range(max(10, a.samples // 10)):
    assign = {v: False for v in primaries}
    order = primaries[:]; rng.shuffle(order)
    for v in order:
        assign[v] = True
        ok, adj = c4free_graph(assign)
        if not ok: assign[v] = False
    greedy.append(assign)
    run(assign, 'greedy maximal C4-free')
    # mutations: add one orbit (creates a C4 by maximality), remove one orbit
    on = [v for v in primaries if assign[v]]; off = [v for v in primaries if not assign[v]]
    if off:
        b = dict(assign); b[rng.choice(off)] = True; run(b, 'greedy + one orbit')
    if on:
        b = dict(assign); b[rng.choice(on)] = False; run(b, 'greedy - one orbit')
degs = []
for assign in greedy:
    ok, adj = c4free_graph(assign); degs.append(min(len(x) for x in adj))
report['greedy_min_degrees'] = sorted(degs)
report['tests'] = len(tests); report['mismatches'] = sum(1 for t in tests if t[1] != t[2] or t[3] != (not t[1]))
report['seconds'] = round(time.time() - t0, 1)
report['by_tag'] = {}
for tag, exp, got, full in tests:
    r = report['by_tag'].setdefault(tag, {'n': 0, 'agree': 0, 'degree_ok': 0, 'c4_ok': 0, 'both_ok': 0})
    r['n'] += 1; r['agree'] += (exp == got and full == (not exp)); r['degree_ok'] += ('degree' not in exp); r['c4_ok'] += ('c4' not in exp); r['both_ok'] += (not exp)
print(json.dumps(report, indent=1))
