#!/usr/bin/env python3
"""(4,4,4,4) H-lift STAGE 2: sound RELAXATION SAT encoding (msg 1853).

Given a stage-1 service witness (taus; all slopes +1 WLOG by per-orphan
reflection, msg 1857), S and D are determined on the 192 orphan
vertices.  Encode existence of H:
  - H simple graph on 192 vertices, 13-regular
  - for every distinct pair (u,v):
      #common_H(u,v) = 0 if D.Adj(u,v) or S(u,v)   [zero-pairs]
      #common_H(u,v) = 1 otherwise                  [one-pairs]
(Exact necessary content of degree_sixteen_zeroLayer_orphan_common_
neighbor_partition / ad40009cb4.  UNSAT => this service configuration
excluded (class kill needs all stage-1 orbits or a WLOG argument).
SAT => inconclusive relaxation model only — NOT a graph witness.)

Structure checks on emit: zero-pairs 3360 = 192 D + 3168 S, S is
33-regular (matches msg 1789 counting identity).  Spectral precheck of
S∪D passed independently (Sol, msg 1858): 12I − A_{S∪D} PSD with
nullity 6, trace identities consistent — no cheap spectral kill, SAT
genuinely required.

Output with --emit: DIMACS CNF hlift4444_<sha256_16>.cnf + manifest
(witness, sizes, hash).  Pilot protocol (msg 1857): signal run without
proof logging, 30-min cutoff; if UNSAT, rerun the identical hashed CNF
with DRAT and verify; then enumerate stage-1 orbits.

Emitted instances (2026-08-10):
  v1 (pre counter-repair, signal pilot only, NOT certificate grade):
     hlift4444_477ff4422e5e4fa2.cnf — 6,190,176 vars / 18,689,664
     clauses.  Equisatisfiable to exact-degree-13 by the 156
     double-count argument (msgs 1862/1863): each vertex has 156
     one-pairs, each requiring one common H-neighbor, and
     156 = sum_{w in N_H(v)} #{one-paired u in N(w)} <= 12*deg(v)
     under at-most-13, forcing deg(v) = 13.
  v2 (counter repaired + 264 cut, certificate grade):
     hlift4444_b229c6f11ab1bcad.cnf — 7,045,596 vars / 23,066,016
     clauses; full SHA-256
     b229c6f11ab1bcad... (see manifest for full digest + rule counts:
     zero_common 638400, one_common_and_exactly_one 17027712,
     degree_13_exact 1978752, A_edge_total_264 3421152; sums to total).
  v3 (THIS encoder, v2 + local odd A-incidence cuts):
     hlift4444_a27456953947a173.cnf — 7,052,124 vars / 23,092,320
     clauses.  For every vertex v, `a_v = |N_H(v) intersect N_A(v)|`
     is odd because `2 t_v = 13 - a_v`, where t_v is the number of
     H-edges induced by N_H(v).  Each 35-literal parity is encoded by a
     chain of 34 equivalence XOR gates and one final unit.  See the
     manifest for the full SHA-256 and test_parity_odd.py for exhaustive
     small-chain tests.
"""
import sys, hashlib, json
from itertools import combinations

# stage-1 witness (taus), slopes all +1, gauge eta=1,c=0
WIT = {
 (0,0): {1:0, 2:4, 3:2}, (0,1): {1:0, 2:5, 3:4},
 (0,2): {1:0, 2:8, 3:1}, (0,3): {1:0, 2:10, 3:5},
 (1,0): {0:0, 2:2, 3:4}, (1,1): {0:0, 2:4, 3:5},
 (1,2): {0:0, 2:7, 3:11}, (1,3): {0:0, 2:11, 3:7},
 (2,0): {0:0, 1:5, 3:1}, (2,1): {0:0, 1:7, 3:2},
 (2,2): {0:0, 1:10, 3:8}, (2,3): {0:0, 1:11, 3:10},
 (3,0): {0:0, 1:1, 2:8}, (3,1): {0:0, 1:2, 2:1},
 (3,2): {0:0, 1:4, 2:5}, (3,3): {0:0, 1:8, 2:10},
}
ORPHANS = sorted(WIT)
oidx = {o: i for i, o in enumerate(ORPHANS)}
N = 192
def vid(o, x): return 12 * oidx[o] + (x % 12)

Dset = set()
for o in ORPHANS:
    for x in range(12):
        Dset.add(frozenset((vid(o, x), vid(o, x + 1))))
Sset = set()
for o1, o2 in combinations(ORPHANS, 2):
    shared = [e for e in WIT[o1] if e in WIT[o2]]
    for e in shared:
        for x in range(12):
            xp = (x + WIT[o1][e] - WIT[o2][e]) % 12
            Sset.add(frozenset((vid(o1, x), vid(o2, xp))))
assert not (Dset & Sset), "S/D overlap would contradict the identity"
deg_S = {}
for fs in Sset:
    for v in fs: deg_S[v] = deg_S.get(v, 0) + 1
assert all(d == 33 for d in deg_S.values()), sorted(set(deg_S.values()))

zero_pairs = Dset | Sset
all_pairs = [frozenset(p) for p in combinations(range(N), 2)]
one_pairs = [p for p in all_pairs if p not in zero_pairs]
print(f"zero-pairs {len(zero_pairs)}  one-pairs {len(one_pairs)}  total {len(all_pairs)}")

RULE_COUNTS = {}
def bump(rule, n=1):
    RULE_COUNTS[rule] = RULE_COUNTS.get(rule, 0) + n

nv = 0
def newvar():
    global nv; nv += 1; return nv
E = {}
for p in all_pairs:
    E[p] = newvar()
clauses = []
mark = len(clauses)

for p in zero_pairs:
    u, v = sorted(p)
    for w in range(N):
        if w == u or w == v: continue
        clauses.append((-E[frozenset((u, w))], -E[frozenset((v, w))]))
bump("zero_common", len(clauses) - mark)
mark = len(clauses)

aux_and = 0
aux_cnt = 0
for p in one_pairs:
    u, v = sorted(p)
    ts = []
    for w in range(N):
        if w == u or w == v: continue
        a, b = E[frozenset((u, w))], E[frozenset((v, w))]
        t = newvar(); aux_and += 1
        clauses.append((-t, a)); clauses.append((-t, b))
        clauses.append((t, -a, -b))
        ts.append(t)
    clauses.append(tuple(ts))
    prev = None
    for t in ts[:-1]:
        s = newvar(); aux_cnt += 1
        if prev is None:
            clauses.append((-t, s))
        else:
            clauses.append((-prev, s)); clauses.append((-t, s))
            clauses.append((-t, -prev))
        prev = s
    if prev is not None:
        clauses.append((-ts[-1], -prev))
bump("one_common_and_exactly_one", len(clauses) - mark)
mark = len(clauses)

def card_eq(lits, k):
    """Exact-k via EQUIVALENCE sequential counter (Sol audit 1862 repair):
    counter bits defined both directions, so the final >=k unit is sound.
    Unit-tested: model count C(n,k) exactly (test_card_eq.py)."""
    global aux_cnt
    # s[i][j] <-> (among first i lits, at least j are true)
    prev = [None] * (k + 2)
    for i, lit in enumerate(lits, 1):
        cur = [None] * (k + 2)
        for j in range(1, min(i, k + 1) + 1):
            cur[j] = newvar(); aux_cnt += 1
            # forward: prev[j] -> cur[j];  lit & prev[j-1] -> cur[j]
            if prev[j] is not None:
                clauses.append((-prev[j], cur[j]))
            if j == 1:
                clauses.append((-lit, cur[1]))
            elif prev[j - 1] is not None:
                clauses.append((-lit, -prev[j - 1], cur[j]))
            # reverse: cur[j] -> prev[j] | (lit & prev[j-1])
            pj = prev[j]
            pj1 = prev[j - 1] if j >= 2 else None
            if j == 1:
                if pj is None:
                    clauses.append((-cur[1], lit))
                else:
                    clauses.append((-cur[1], pj, lit))
            else:
                if pj is None and pj1 is None:
                    clauses.append((-cur[j],))     # unreachable count
                elif pj is None:
                    clauses.append((-cur[j], lit))
                    clauses.append((-cur[j], pj1))
                else:
                    clauses.append((-cur[j], pj, lit))
                    clauses.append((-cur[j], pj, pj1))
        # at-most-k: lit & prev[k] -> false
        if prev[k] is not None:
            clauses.append((-lit, -prev[k]))
        prev = cur
    if prev[k] is None or k == 0:
        raise RuntimeError
    clauses.append((prev[k],))   # >= k (now sound: bits are equivalences)

for v in range(N):
    lits = [E[frozenset((v, w))] for w in range(N) if w != v]
    card_eq(lits, 13)
bump("degree_13_exact", len(clauses) - mark)
mark = len(clauses)
# ---- redundant derived cuts (Sol msg 1861; logically implied, aid
# propagation): |E(H) ∩ (S∪D)| = 264 globally.
A_lits = [E[p] for p in zero_pairs]
card_eq(A_lits, 264)
bump("A_edge_total_264", len(clauses) - mark)
mark = len(clauses)

def xor_odd(lits):
    """Assert XOR(lits) = true using equivalence Tseitin gates.

    Each new gate z is defined by z <-> (x XOR y), so every input
    assignment has exactly one extension to the auxiliaries.  The final
    positive unit selects precisely the odd-parity inputs.
    """
    if not lits:
        clauses.append(())
        return
    acc = lits[0]
    for lit in lits[1:]:
        z = newvar()
        # z <-> acc XOR lit
        clauses.append((-acc, -lit, -z))
        clauses.append((-acc, lit, z))
        clauses.append((acc, -lit, z))
        clauses.append((acc, lit, -z))
        acc = z
    clauses.append((acc,))

for v in range(N):
    A_neighbor_lits = [E[frozenset((v, w))]
                       for w in range(N)
                       if w != v and frozenset((v, w)) in zero_pairs]
    assert len(A_neighbor_lits) == 35
    xor_odd(A_neighbor_lits)
bump("local_A_incidence_odd", len(clauses) - mark)

print(f"vars {nv}  clauses {len(clauses)}  (edge {len(all_pairs)}, and-aux {aux_and}, cnt-aux {aux_cnt})")

if "--emit" in sys.argv:
    import io
    buf = io.StringIO()
    buf.write(f"p cnf {nv} {len(clauses)}\n")
    for c in clauses:
        buf.write(" ".join(map(str, c)) + " 0\n")
    data = buf.getvalue().encode()
    h = hashlib.sha256(data).hexdigest()[:16]
    fn = f"hlift4444_{h}.cnf"
    open(fn, "wb").write(data)
    json.dump({"witness": {str(k): v for k, v in WIT.items()},
               "zero_pairs": len(zero_pairs), "one_pairs": len(one_pairs),
               "vars": nv, "clauses": len(clauses),
               "sha256": hashlib.sha256(data).hexdigest(),
               "rule_counts": RULE_COUNTS},
              open(f"hlift4444_{h}.manifest.json", "w"), indent=1)
    print("wrote", fn)
