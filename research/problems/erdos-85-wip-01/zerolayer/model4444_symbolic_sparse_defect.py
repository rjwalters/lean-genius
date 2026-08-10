#!/usr/bin/env python3
"""Exact symbolic CNF for a sparse center using a defect neighbor.

The phase variables quantify over every corrected Stage-1 (4,4,4,4)
service witness.  The selected 13-set X is a candidate H-neighborhood of
vertex ((0,0),0), with its forward defect neighbor selected as the unique
A-neighbor of the center.  X is A-independent and has exact 4/4/4 color
balance for paired component 1.  UNSAT excludes this local branch for the
entire normalized class; SAT must pass the independent semantic verifier.

Normalization is lossless: omitted types relabel the paired involution to
(01)(23); the four copies of one omitted type are unlabeled, putting the
candidate block at copy zero; simultaneous translation of all orphan C12
coordinates puts its center at zero after the per-orphan phase gauge; and
simultaneous reflection reverses the two defect directions.  We deliberately
do not add copy ordering or residual phase anchors after fixing the candidate.
"""

import hashlib
from itertools import combinations
import io
import json
from pathlib import Path
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


def card_eq_binary(literals, k):
    """Exact cardinality through an equivalence binary ripple counter."""
    width = (len(literals) + 1).bit_length()
    previous = [None] * width
    for literal in literals:
        carry = literal
        current = []
        for bit in range(width):
            old = previous[bit]
            if old is None:
                current.append(carry)
                carry = None
            elif carry is None:
                current.append(old)
            else:
                result = newvar()
                clauses.extend([
                    (-old, -carry, -result), (-old, carry, result),
                    (old, -carry, result), (old, carry, -result),
                ])
                next_carry = newvar()
                clauses.extend([
                    (-next_carry, old), (-next_carry, carry),
                    (next_carry, -old, -carry),
                ])
                current.append(result)
                carry = next_carry
        previous = current
    for bit, literal in enumerate(previous):
        if literal is None:
            assert not ((k >> bit) & 1)
        else:
            clauses.append((literal,) if (k >> bit) & 1 else (-literal,))


def card_eq_sequential(literals, k):
    """Exact cardinality with equivalence-defined threshold bits."""
    previous = [None] * (k + 2)
    for index, literal in enumerate(literals, 1):
        current = [None] * (k + 2)
        for threshold in range(1, min(index, k + 1) + 1):
            current[threshold] = newvar()
            if previous[threshold] is not None:
                clauses.append((-previous[threshold], current[threshold]))
            if threshold == 1:
                clauses.append((-literal, current[1]))
            elif previous[threshold - 1] is not None:
                clauses.append((-literal, -previous[threshold - 1],
                                current[threshold]))
            same = previous[threshold]
            lower = previous[threshold - 1] if threshold >= 2 else None
            if threshold == 1:
                clauses.append((-current[1], literal) if same is None else
                               (-current[1], same, literal))
            elif same is None and lower is None:
                clauses.append((-current[threshold],))
            elif same is None:
                clauses.extend([(-current[threshold], literal),
                                (-current[threshold], lower)])
            else:
                clauses.extend([(-current[threshold], same, literal),
                                (-current[threshold], same, lower)])
        if previous[k] is not None:
            clauses.append((-literal, -previous[k]))
        previous = current
    clauses.append((previous[k],))


# Gauge-fixed link phases.  No copy-ordering or used-component symmetry is
# imposed: fixing the candidate in copy zero must not silently retain a
# conflicting copy symmetry break.
mark = len(clauses)
P = {}
for orphan in ORPHANS:
    for component in links(orphan):
        row = []
        for phase in range(12):
            P[orphan, component, phase] = newvar()
            row.append(P[orphan, component, phase])
        exactly_one_pairwise(row)
    clauses.append((P[orphan, links(orphan)[0], 0],))
    for e, f in combinations(links(orphan), 2):
        for a in range(12):
            for b in range(12):
                if a % 3 == b % 3:
                    clauses.append((-P[orphan, e, a], -P[orphan, f, b]))
bump("stage1_phase_onehot_gauge_row_residues", mark)

# Exact phase differences and the corrected pair-injectivity law.
mark = len(clauses)
DELTA = {}
for o1, o2 in combinations(ORPHANS, 2):
    shared = sorted(set(links(o1)) & set(links(o2)))
    for component in shared:
        row = []
        for residue in range(12):
            DELTA[o1, o2, component, residue] = newvar()
            row.append(DELTA[o1, o2, component, residue])
        exactly_one_pairwise(row)
        for a in range(12):
            for b in range(12):
                clauses.append((-P[o1, component, a],
                                -P[o2, component, b],
                                DELTA[o1, o2, component, (a - b) % 12]))
    for e, f in combinations(shared, 2):
        for residue in range(12):
            clauses.append((-DELTA[o1, o2, e, residue],
                            -DELTA[o1, o2, f, residue]))
bump("stage1_delta_definition_and_pair_injectivity", mark)

# Symbolic service adjacency for every cross-block vertex pair.
mark = len(clauses)
SERVICE = {}
for o1, o2 in combinations(ORPHANS, 2):
    shared = sorted(set(links(o1)) & set(links(o2)))
    for x in range(12):
        for y in range(12):
            service = newvar()
            SERVICE[frozenset((vid(o1, x), vid(o2, y)))] = service
            witnesses = [DELTA[o1, o2, e, (y - x) % 12] for e in shared]
            for witness in witnesses:
                clauses.append((-witness, service))
            clauses.append((-service, *witnesses))
bump("symbolic_service_adjacency", mark)

# Candidate H-neighborhood.
mark = len(clauses)
X = [newvar() for _ in range(N)]
center = vid((0, 0), 0)
forward = vid((0, 0), 1)
backward = vid((0, 0), -1)
clauses.extend([(-X[center],), (X[forward],), (-X[backward],)])
card_eq_binary(X, 13)
bump("candidate_size_and_defect_overlap_pin", mark)

# An H-neighborhood is A-independent: any two members already have center
# as an H-common-neighbor, whereas A marks zero-common-neighbor pairs.
mark = len(clauses)
for orphan in ORPHANS:
    for x in range(12):
        clauses.append((-X[vid(orphan, x)], -X[vid(orphan, x + 1)]))
for pair, service in SERVICE.items():
    left, right = tuple(pair)
    clauses.append((-X[left], -X[right], -service))
bump("candidate_A_independent", mark)

# The selected forward defect neighbor is the unique A-neighbor of center.
mark = len(clauses)
for vertex in range(N):
    if vertex // 12 == center // 12:
        continue
    clauses.append((-X[vertex], -SERVICE[frozenset((center, vertex))]))
bump("defect_neighbor_is_unique_center_overlap", mark)

# Exact 4/4/4 H-color balance for paired component e=1.  A vertex in a
# block linked to e has color coordinate+tau[o,e] mod 3.  Twelve selected
# linked vertices plus |X|=13 automatically leave one omitted-e vertex.
mark = len(clauses)
selected_color = [[] for _ in range(3)]
for orphan in ORPHANS:
    if 1 not in links(orphan):
        continue
    for x in range(12):
        selected = X[vid(orphan, x)]
        for phase in range(12):
            both = newvar()
            phase_literal = P[orphan, 1, phase]
            clauses.extend([
                (-both, selected), (-both, phase_literal),
                (both, -selected, -phase_literal),
            ])
            selected_color[(x + phase) % 3].append(both)
for color in range(3):
    if "--sequential-color" in sys.argv:
        card_eq_sequential(selected_color[color], 4)
    else:
        card_eq_binary(selected_color[color], 4)
bump("paired_component_exact_color_balance", mark)

print(f"vars {nv} clauses {len(clauses)} phases {len(P)} "
      f"delta {len(DELTA)} service {len(SERVICE)} selected {len(X)}")

if "--emit" in sys.argv:
    buffer = io.StringIO()
    buffer.write(f"p cnf {nv} {len(clauses)}\n")
    for clause in clauses:
        buffer.write(" ".join(map(str, clause)) + " 0\n")
    data = buffer.getvalue().encode()
    digest = hashlib.sha256(data).hexdigest()
    stem = f"sparse_defect_symbolic_{digest[:16]}"
    Path(stem + ".cnf").write_bytes(data)
    verifier = Path(__file__).with_name(
        "verify_symbolic_sparse_defect_assignment.py")
    manifest = {
        "scope": "all corrected Stage-1 (4,4,4,4) phases with a sparse "
                 "center using its forward defect neighbor",
        "encoder_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "sat_verifier_sha256": hashlib.sha256(verifier.read_bytes()).hexdigest(),
        "vars": nv, "clauses": len(clauses), "sha256": digest,
        "phase_variables": len(P), "delta_variables": len(DELTA),
        "service_variables": len(SERVICE), "selection_variables": len(X),
        "rule_counts": rule_counts,
        "normalization": {"source_omit": 0, "paired_component": 1,
                          "source_copy": 0, "center_coordinate": 0,
                          "defect_neighbor_coordinate": 1,
                          "copy_ordering": False, "phase_symmetry": False},
        "options": {"sequential_color": "--sequential-color" in sys.argv},
    }
    Path(stem + ".manifest.json").write_text(json.dumps(manifest, indent=1) + "\n")
    print("wrote", stem)
