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

if "--phase-symmetry" in sys.argv:
    mark = len(clauses)
    # The four orphan components of each omitted type are unlabeled.  Sort
    # them by the phase on their second linked used component.
    for omit in COMPS:
        second = links((omit, 0))[1]
        for copy in range(3):
            for left in range(12):
                for right in range(left):
                    clauses.append((-P[(omit, copy), second, left],
                                    -P[(omit, copy + 1), second, right]))
    # Residual rotations of each used C12 by multiples of three act on link
    # phases, followed by the already-imposed per-orphan first-link regauge.
    # Modulo a common rotation, the three relative rotations uniquely bring
    # these anchors into their canonical residue representatives 0,1,2.
    for orphan, component in [((0, 0), 2), ((0, 0), 3), ((1, 0), 2)]:
        clauses.append(tuple(P[orphan, component, phase]
                             for phase in range(3)))
    bump("stage1_copy_and_used_rotation_symmetry", mark)

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


def xor_odd(literals):
    """Assert odd parity with equivalence-defined XOR Tseitin gates."""
    accumulator = literals[0]
    for literal in literals[1:]:
        result = newvar()
        clauses.append((-accumulator, -literal, -result))
        clauses.append((-accumulator, literal, result))
        clauses.append((accumulator, -literal, result))
        clauses.append((accumulator, literal, -result))
        accumulator = result
    clauses.append((accumulator,))


if "--local-parity" in sys.argv:
    # Formally justified by
    # `triangleFreeNeighbors_card_mod_two_eq_vertexDegree`: A = D union S
    # marks precisely the zero-common pairs, and H has odd degree thirteen.
    mark = len(clauses)
    service_H = {}
    for pair, service in SERVICE.items():
        both = newvar()
        edge = E[pair]
        clauses.append((-both, edge))
        clauses.append((-both, service))
        clauses.append((both, -edge, -service))
        service_H[pair] = both
    for vertex in range(N):
        local = []
        for other in range(N):
            if other == vertex:
                continue
            pair = frozenset((vertex, other))
            if pair in Dset:
                local.append(E[pair])
            elif pair in service_H:
                local.append(service_H[pair])
        assert len(local) == 182  # two D candidates plus 180 cross-block
        xor_odd(local)
    bump("symbolic_local_A_incidence_odd", mark)


def mod3_eq_one(literals):
    """Assert that the number of true literals is one modulo three."""
    # One-hot states record the exact prefix residue.  The two implication
    # directions for each input value, together with one-hotness, make every
    # transition deterministic (and give every valid input a unique state
    # extension).
    previous = [newvar() for _ in range(3)]
    exactly_one_pairwise(previous)
    clauses.append((previous[0],))
    clauses.append((-previous[1],))
    clauses.append((-previous[2],))
    for literal in literals:
        current = [newvar() for _ in range(3)]
        exactly_one_pairwise(current)
        for residue in range(3):
            clauses.append((-previous[residue], literal, current[residue]))
            clauses.append((-previous[residue], -literal,
                            current[(residue + 1) % 3]))
        previous = current
    clauses.append((previous[1],))


if "--type-balance" in sys.argv or "--type-profile" in sys.argv:
    # The cube-root Fourier kernel of A=D union S is annihilated by H.  If
    # q_e(v) counts H-neighbors in blocks linked to used component e, this
    # gives 3 | q_e(v).  Its complement among the thirteen H-neighbors is the
    # count in blocks omitting e, hence that count is 1 mod 3.  Consequently
    # every vertex has omitted-type profile [10,1,1,1], [7,4,1,1], or
    # [4,4,4,1].
    mark = len(clauses)
    for vertex in range(N):
        for omit in COMPS:
            candidates = [
                E[frozenset((vertex, other))]
                for other in range(N)
                if other != vertex and ORPHANS[other // 12][0] == omit
            ]
            assert len(candidates) in (47, 48)
            mod3_eq_one(candidates)
    bump("cube_root_kernel_omitted_type_balance", mark)


def card_at_most(literals, k):
    """Sequential threshold encoding of cardinality at most k."""
    previous = [None] * (k + 1)
    for index, literal in enumerate(literals, 1):
        current = [None] * (k + 1)
        for threshold in range(1, min(index, k) + 1):
            current[threshold] = newvar()
            if threshold == 1:
                clauses.append((-literal, current[1]))
            if previous[threshold] is not None:
                clauses.append((-previous[threshold], current[threshold]))
            if threshold >= 2 and previous[threshold - 1] is not None:
                clauses.append((-literal, -previous[threshold - 1],
                                current[threshold]))
        if previous[k] is not None:
            clauses.append((-literal, -previous[k]))
        previous = current


if "--type-profile" in sys.argv:
    # Summing within-type common-neighbor cherries forces equality in the
    # minimum profile bound: every omitted-type count is at most four.  With
    # the preceding 1 mod 3 cuts and total degree thirteen, the four counts
    # are therefore exactly a permutation of [4,4,4,1].
    mark = len(clauses)
    for vertex in range(N):
        for omit in COMPS:
            candidates = [
                E[frozenset((vertex, other))]
                for other in range(N)
                if other != vertex and ORPHANS[other // 12][0] == omit
            ]
            card_at_most(candidates, 4)
    bump("within_type_cherry_profile_cap", mark)


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


if "--paired-type-quotient" in sys.argv:
    # The exact [4,4,4,1] profiles define four balanced sparse fibers.  The
    # H^2=9 eigenspace has dimension three, so their contrast space equals
    # the omitted-type contrast space; hence the sparse fibers are the four
    # omitted-type classes up to a permutation.  Symmetry makes that
    # permutation an involution, and the fixed (+3)^2,(-3)^1 sign split
    # forces two disjoint transpositions.  Type relabeling normalizes the
    # pairing to (0 1)(2 3).  Thus every vertex has one neighbor in its
    # paired omitted class and four in each other omitted class.
    mark = len(clauses)
    paired = {0: 1, 1: 0, 2: 3, 3: 2}
    for vertex in range(N):
        source_omit = ORPHANS[vertex // 12][0]
        for target_omit in COMPS:
            candidates = [
                E[frozenset((vertex, other))]
                for other in range(N)
                if other != vertex and
                ORPHANS[other // 12][0] == target_omit
            ]
            expected = 1 if target_omit == paired[source_omit] else 4
            card_eq(candidates, expected)
    bump("paired_omitted_type_equitable_quotient", mark)


if "--color-balance" in sys.argv:
    if "--paired-type-quotient" not in sys.argv:
        raise ValueError("--color-balance requires --paired-type-quotient")
    # The full cube-root kernel is stronger than its omitted-type degree
    # consequence.  For each used component e, H annihilates the two rational
    # contrasts between the three colors x + tau[o,e] (mod 3).  Hence every
    # vertex has equally many H-neighbors in all three linked-e colors.  The
    # paired quotient says that the total linked-e degree is twelve when e is
    # paired with the vertex's omitted type, and nine otherwise, so every
    # color count is respectively four or three.
    mark = len(clauses)
    color = {}
    for orphan in ORPHANS:
        for component in links(orphan):
            for residue in range(3):
                literal = newvar()
                color[orphan, component, residue] = literal
                phases = [P[orphan, component, phase]
                          for phase in range(12) if phase % 3 == residue]
                for phase_literal in phases:
                    clauses.append((-phase_literal, literal))
                clauses.append((-literal, *phases))
    paired = {0: 1, 1: 0, 2: 3, 3: 2}
    for vertex in range(N):
        source_omit = ORPHANS[vertex // 12][0]
        for component in COMPS:
            expected = 4 if component == paired[source_omit] else 3
            for residue in range(3):
                candidates = []
                for other in range(N):
                    if other == vertex:
                        continue
                    orphan = ORPHANS[other // 12]
                    if component not in links(orphan):
                        continue
                    # The color of (orphan,x) is x+tau[o,e], so translate the
                    # requested vertex color back to the phase residue.
                    x = other % 12
                    phase_residue = (residue - x) % 3
                    edge = E[frozenset((vertex, other))]
                    colored = color[orphan, component, phase_residue]
                    both = newvar()
                    clauses.append((-both, edge))
                    clauses.append((-both, colored))
                    clauses.append((both, -edge, -colored))
                    candidates.append(both)
                assert len(candidates) in (143, 144)
                card_eq(candidates, expected)
    bump("cube_root_kernel_exact_color_balance", mark)


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
        "encoder_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "sat_verifier_sha256": hashlib.sha256(
            Path(__file__).with_name("verify_symbolic_hlift_assignment.py")
            .read_bytes()).hexdigest(),
        "vars": nv, "clauses": len(clauses), "sha256": digest,
        "edge_variables": len(E), "phase_variables": len(P),
        "delta_variables": len(DELTA), "service_variables": len(SERVICE),
        "common_and_variables": and_aux, "rule_counts": rule_counts,
        "options": {
            "local_parity": "--local-parity" in sys.argv,
            "phase_symmetry": "--phase-symmetry" in sys.argv,
            "type_balance": "--type-balance" in sys.argv,
            "type_profile": "--type-profile" in sys.argv,
            "paired_type_quotient": "--paired-type-quotient" in sys.argv,
            "color_balance": "--color-balance" in sys.argv,
        },
    }
    json.dump(manifest, open(stem + ".manifest.json", "w"), indent=1)
    print("wrote", stem)
