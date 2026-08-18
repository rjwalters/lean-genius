#!/usr/bin/env python3
"""Signal-only CNF for two sparse centers in one normalized orphan block.

This deliberately reuses the exact phase/service prefix of the certified
single-center encoder, then adds two candidate H-neighborhoods.  It is a
research probe, not a certificate encoder: any useful UNSAT branch must be
moved into a standalone audited encoder before it is claimed.
"""

import io
from pathlib import Path
import sys


distance = int(sys.argv[1])
assert 1 <= distance <= 6

# Reuse only the exact corrected Stage-1 phase and symbolic-service builder.
source_path = Path(__file__).with_name("model4444_symbolic_sparse_defect.py")
prefix = source_path.read_text().split("# Candidate H-neighborhood.", 1)[0]
namespace = {"__file__": str(source_path), "__name__": "two_sparse_prefix"}
exec(compile(prefix, str(source_path), "exec"), namespace)
globals().update(namespace)

if "--fix-baseline" in sys.argv:
    from test_symbolic_hlift_service import WIT
    for orphan in ORPHANS:
        for component in links(orphan):
            clauses.append((P[orphan, component, WIT[orphan][component]],))


def candidate_neighborhood(center):
    selected = [newvar() for _ in range(N)]
    clauses.append((-selected[center],))
    card_eq_binary(selected, 13)

    # A-independence.
    for orphan in ORPHANS:
        for x in range(12):
            clauses.append((-selected[vid(orphan, x)],
                            -selected[vid(orphan, x + 1)]))
    for pair, service in SERVICE.items():
        left, right = tuple(pair)
        clauses.append((-selected[left], -selected[right], -service))

    # Exactly one A-neighbor of the center lies in this H-neighborhood.
    overlaps = [selected[(center - 1) % 12], selected[(center + 1) % 12]]
    if "--color-preservation" in sys.argv:
        # Certified separately by the cb059967... DRAT certificate.
        clauses.extend([(-literal,) for literal in overlaps])
    for vertex in range(N):
        if vertex // 12 == center // 12:
            continue
        overlap = newvar()
        service = SERVICE[frozenset((center, vertex))]
        clauses.extend([(-overlap, selected[vertex]), (-overlap, service),
                        (overlap, -selected[vertex], -service)])
        overlaps.append(overlap)
        if "--color-preservation" in sys.argv:
            orphan = ORPHANS[vertex // 12]
            if 1 not in links(orphan):
                clauses.append((-overlap,))
            else:
                center_color = center % 3
                coordinate = vertex % 12
                for phase in range(12):
                    if (coordinate + phase) % 3 != center_color:
                        clauses.append((-overlap, -P[orphan, 1, phase]))
    card_eq_sequential(overlaps, 1)

    # Exact paired-component color balance.  The source block has phase zero
    # in component 1, so its center color is center mod 3; balance itself is
    # always four vertices in each of the three colors.
    selected_color = [[] for _ in range(3)]
    for orphan in ORPHANS:
        if 1 not in links(orphan):
            continue
        for x in range(12):
            literal = selected[vid(orphan, x)]
            for phase in range(12):
                both = newvar()
                phase_literal = P[orphan, 1, phase]
                clauses.extend([
                    (-both, literal), (-both, phase_literal),
                    (both, -literal, -phase_literal),
                ])
                selected_color[(x + phase) % 3].append(both)
    for color in range(3):
        card_eq_sequential(selected_color[color], 4)
    return selected


def threshold_bits(literals, maximum):
    """Equivalence-defined bits saying at least k literals are true."""
    previous = [None] * (maximum + 1)
    for index, literal in enumerate(literals, 1):
        current = [None] * (maximum + 1)
        for threshold in range(1, min(index, maximum) + 1):
            bit = newvar()
            current[threshold] = bit
            same = previous[threshold]
            lower = previous[threshold - 1] if threshold >= 2 else None
            if same is not None:
                clauses.append((-same, bit))
            if threshold == 1:
                clauses.append((-literal, bit))
                clauses.append((-bit, literal) if same is None else
                               (-bit, same, literal))
            elif lower is not None:
                clauses.append((-literal, -lower, bit))
                if same is None:
                    clauses.extend([(-bit, literal), (-bit, lower)])
                else:
                    clauses.extend([(-bit, same, literal),
                                    (-bit, same, lower)])
            elif same is None:
                clauses.append((-bit,))
            else:
                clauses.append((-bit, same))
        previous = current
    return previous


def mixed_row_thresholds(selected):
    """Threshold representation of |N_H(center) intersect N_A(target)|."""
    rows = []
    for target in range(N):
        block_base = 12 * (target // 12)
        coordinate = target % 12
        neighbors = [selected[block_base + (coordinate - 1) % 12],
                     selected[block_base + (coordinate + 1) % 12]]
        for source in range(N):
            if source // 12 == target // 12:
                continue
            both = newvar()
            service = SERVICE[frozenset((source, target))]
            clauses.extend([(-both, selected[source]), (-both, service),
                            (both, -selected[source], -service)])
            neighbors.append(both)
        thresholds = threshold_bits(neighbors, 10)
        clauses.append((-thresholds[10],))  # certified B-entry cap
        rows.append(thresholds)
    return rows


left_center = vid((0, 0), 0)
right_center = vid((0, 0), distance)
X = candidate_neighborhood(left_center)
Z = candidate_neighborhood(right_center)

# H is symmetric at the two centers.
clauses.extend([
    (-X[right_center], Z[left_center]),
    (X[right_center], -Z[left_center]),
])

# H^2 = 12I + J - A: same-block centers have zero common H-neighbors
# at defect distance one and exactly one at every other distance here.
common = []
for vertex in range(N):
    both = newvar()
    clauses.extend([(-both, X[vertex]), (-both, Z[vertex]),
                    (both, -X[vertex], -Z[vertex])])
    common.append(both)
if distance == 1:
    clauses.extend([(-literal,) for literal in common])
else:
    card_eq_sequential(common, 1)

# BH = H^2 A fixes the ordered A-edge mass from N_H(left) to N_H(right).
# For distances 1,...,6 the exact values are the pointwise ledger below.
if "--cross-mass" in sys.argv:
    cross_edges = []
    for left in range(N):
        for right in range(N):
            if left // 12 == right // 12:
                if (right - left) % 12 not in (1, 11):
                    continue
                both = newvar()
                clauses.extend([(-both, X[left]), (-both, Z[right]),
                                (both, -X[left], -Z[right])])
            else:
                service = SERVICE[frozenset((left, right))]
                both = newvar()
                clauses.extend([(-both, X[left]), (-both, Z[right]),
                                (-both, service),
                                (both, -X[left], -Z[right], -service)])
            cross_edges.append(both)
    card_eq_binary(cross_edges, [44, 31, 29, 32, 32, 29][distance - 1])

if "--row-geometry" in sys.argv:
    left_row = mixed_row_thresholds(X)
    right_row = mixed_row_thresholds(Z)
    for row in (left_row, right_row):
        weighted = []
        for thresholds in row:
            for level in range(1, 10):
                weighted.extend([thresholds[level]] * (2 * level - 1))
        card_eq_binary(weighted, 1255)
        for target_type in range(4):
            type_mass = [
                thresholds[level]
                for target, thresholds in enumerate(row)
                if ORPHANS[target // 12][0] == target_type
                for level in range(1, 10)
            ]
            card_eq_binary(type_mass, 107 if target_type == 1 else 116)

    dot_terms = []
    for target in range(N):
        for left_level in range(1, 10):
            for right_level in range(1, 10):
                both = newvar()
                left_bit = left_row[target][left_level]
                right_bit = right_row[target][right_level]
                clauses.extend([(-both, left_bit), (-both, right_bit),
                                (both, -left_bit, -right_bit)])
                dot_terms.append(both)
    card_eq_binary(dot_terms,
                   [997, 1093, 1068, 1081, 1081, 1069][distance - 1])

final_nv = namespace["nv"]
print(f"distance {distance} vars {final_nv} clauses {len(clauses)}")
if "--emit" in sys.argv:
    suffix = "_fixed_types" if "--fix-baseline" in sys.argv else ""
    output = Path(f"/tmp/two_sparse_d{distance}{suffix}.cnf")
    with output.open("w") as handle:
        handle.write(f"p cnf {final_nv} {len(clauses)}\n")
        for clause in clauses:
            handle.write(" ".join(map(str, clause)) + " 0\n")
    print(output)
