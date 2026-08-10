#!/usr/bin/env python3
"""Class-level SAT relaxation for every (4,4,4,4) service witness.

The 48 link phases are variables.  One-hot phase differences define service
adjacency symbolically, so one CNF quantifies over the entire corrected
Stage-1 class.  H is 13-regular; D-pairs have zero common H-neighbors; for
every other pair the common-neighbor count is zero on a service pair and one
otherwise.  UNSAT therefore kills the full service class.  SAT remains only
a relaxation witness and must be independently checked.
"""

import hashlib
from itertools import combinations
import io
import json
import sys

COMPS = range(4)
ORPHANS = [(omit, copy) for omit in COMPS for copy in range(4)]
OIDX = {orphan: index for index, orphan in enumerate(ORPHANS)}
N = 192


def links(orphan):
    return [e for e in COMPS if e != orphan[0]]


def vid(orphan, x):
    return 12 * OIDX[orphan] + x % 12


nv = 0
clauses = []
rule_counts = {}


def newvar():
    global nv
    nv += 1
    return nv


def bump(name, mark):
    rule_counts[name] = len(clauses) - mark


def exactly_one_pairwise(literals):
    clauses.append(tuple(literals))
    for left, right in combinations(literals, 2):
        clauses.append((-left, -right))


# Edge variables remain first and in the same combinations-order as the
# fixed-WIT encoder, allowing the independent structural verifier to reuse
# its edge extraction logic.
all_pairs = [frozenset(pair) for pair in combinations(range(N), 2)]
E = {pair: newvar() for pair in all_pairs}

# P[o,e,a] means link phase tau[o,e] = a in Z/12.
mark = len(clauses)
P = {}
for orphan in ORPHANS:
    for component in links(orphan):
        literals = []
        for phase in range(12):
            P[orphan, component, phase] = newvar()
            literals.append(P[orphan, component, phase])
        exactly_one_pairwise(literals)
    first = links(orphan)[0]
    clauses.append((P[orphan, first, 0],))
    # Row offsets are pairwise distinct modulo three.
    for e, f in combinations(links(orphan), 2):
        for a in range(12):
            for b in range(12):
                if a % 3 == b % 3:
                    clauses.append((-P[orphan, e, a], -P[orphan, f, b]))
bump("stage1_phase_onehot_gauge_row_residues", mark)

# DELTA[o1,o2,e,r] means tau[o1,e] - tau[o2,e] = r mod 12.
mark = len(clauses)
DELTA = {}
for o1, o2 in combinations(ORPHANS, 2):
    shared = sorted(set(links(o1)) & set(links(o2)))
    for component in shared:
        literals = []
        for residue in range(12):
            DELTA[o1, o2, component, residue] = newvar()
            literals.append(DELTA[o1, o2, component, residue])
        exactly_one_pairwise(literals)
        for a in range(12):
            for b in range(12):
                residue = (a - b) % 12
                clauses.append((-P[o1, component, a],
                                -P[o2, component, b],
                                DELTA[o1, o2, component, residue]))
    # Pair injectivity: shared-component differences are all distinct.
    for e, f in combinations(shared, 2):
        for residue in range(12):
            clauses.append((-DELTA[o1, o2, e, residue],
                            -DELTA[o1, o2, f, residue]))
bump("stage1_delta_definition_and_pair_injectivity", mark)

# Symbolic service adjacency for every pair in distinct orphan blocks.
mark = len(clauses)
SERVICE = {}
for o1, o2 in combinations(ORPHANS, 2):
    shared = sorted(set(links(o1)) & set(links(o2)))
    for x in range(12):
        for y in range(12):
            pair = frozenset((vid(o1, x), vid(o2, y)))
            service = newvar()
            SERVICE[pair] = service
            witnesses = [DELTA[o1, o2, component, (y - x) % 12]
                         for component in shared]
            # service <-> OR witnesses. Pair injectivity makes at most one
            # witness true, but the equivalence itself does not rely on that.
            for witness in witnesses:
                clauses.append((-witness, service))
            clauses.append((-service, *witnesses))
bump("symbolic_service_adjacency", mark)

Dset = set()
for orphan in ORPHANS:
    for x in range(12):
        Dset.add(frozenset((vid(orphan, x), vid(orphan, x + 1))))
assert len(Dset) == 192

# Fixed D pairs require zero common neighbors.
mark = len(clauses)
for pair in Dset:
    u, v = sorted(pair)
    for w in range(N):
        if w != u and w != v:
            clauses.append((-E[frozenset((u, w))],
                            -E[frozenset((v, w))]))
bump("defect_zero_common", mark)


def conditional_at_most_one(literals, condition):
    """If `condition` is false, at most one literal may be true."""
    previous = None
    for literal in literals[:-1]:
        seen = newvar()
        if previous is None:
            clauses.append((-literal, seen))
        else:
            clauses.append((-previous, seen))
            clauses.append((-literal, seen))
            clauses.append((-literal, -previous) if condition is None else
                           (condition, -literal, -previous))
        previous = seen
    if previous is not None:
        clauses.append((-literals[-1], -previous) if condition is None else
                       (condition, -literals[-1], -previous))


# Every non-D pair has zero common neighbors when SERVICE, exactly one when
# not SERVICE.  Same-block non-D pairs can never be service pairs, represented
# by the constant-false case below.
mark = len(clauses)
and_aux = 0
for pair in all_pairs:
    if pair in Dset:
        continue
    u, v = sorted(pair)
    service = SERVICE.get(pair)
    common = []
    for w in range(N):
        if w == u or w == v:
            continue
        a = E[frozenset((u, w))]
        b = E[frozenset((v, w))]
        both = newvar()
        and_aux += 1
        clauses.append((-both, a))
        clauses.append((-both, b))
        clauses.append((both, -a, -b))
        common.append(both)
        if service is not None:
            clauses.append((-service, -both))
    if service is None:
        clauses.append(tuple(common))
        conditional_at_most_one(common, None)
    else:
        clauses.append((service, *common))
        conditional_at_most_one(common, service)
bump("conditional_common_neighbor_partition", mark)


def card_eq(literals, k):
    """Exact cardinality via equivalence sequential threshold bits."""
    previous = [None] * (k + 2)
    for i, literal in enumerate(literals, 1):
        current = [None] * (k + 2)
        for j in range(1, min(i, k + 1) + 1):
            current[j] = newvar()
            if previous[j] is not None:
                clauses.append((-previous[j], current[j]))
            if j == 1:
                clauses.append((-literal, current[1]))
            elif previous[j - 1] is not None:
                clauses.append((-literal, -previous[j - 1], current[j]))
            pj = previous[j]
            pj1 = previous[j - 1] if j >= 2 else None
            if j == 1:
                clauses.append((-current[1], literal) if pj is None else
                               (-current[1], pj, literal))
            elif pj is None and pj1 is None:
                clauses.append((-current[j],))
            elif pj is None:
                clauses.append((-current[j], literal))
                clauses.append((-current[j], pj1))
            else:
                clauses.append((-current[j], pj, literal))
                clauses.append((-current[j], pj, pj1))
        if previous[k] is not None:
            clauses.append((-literal, -previous[k]))
        previous = current
    clauses.append((previous[k],))


mark = len(clauses)
for vertex in range(N):
    incident = [E[frozenset((vertex, other))]
                for other in range(N) if other != vertex]
    card_eq(incident, 13)
bump("degree_13_exact", mark)

print(f"vars {nv} clauses {len(clauses)} edge {len(E)} phase {len(P)} "
      f"delta {len(DELTA)} service {len(SERVICE)} and {and_aux}")

if "--emit" in sys.argv:
    buffer = io.StringIO()
    buffer.write(f"p cnf {nv} {len(clauses)}\n")
    for clause in clauses:
        # `None` is used only as a constant-false condition and never enters
        # a clause in the fixed same-block branch.
        assert all(literal is not None for literal in clause)
        buffer.write(" ".join(map(str, clause)) + " 0\n")
    data = buffer.getvalue().encode()
    digest = hashlib.sha256(data).hexdigest()
    stem = f"hlift4444_symbolic_{digest[:16]}"
    open(stem + ".cnf", "wb").write(data)
    manifest = {
        "scope": "all corrected Stage-1 (4,4,4,4) service witnesses",
        "vars": nv, "clauses": len(clauses), "sha256": digest,
        "edge_variables": len(E), "phase_variables": len(P),
        "delta_variables": len(DELTA), "service_variables": len(SERVICE),
        "common_and_variables": and_aux, "rule_counts": rule_counts,
    }
    json.dump(manifest, open(stem + ".manifest.json", "w"), indent=1)
    print("wrote", stem)
