#!/usr/bin/env python3
"""Combine branch partitions with defect weight-class feasibility at q=8.

This is a discovery census, not a proof certificate.  It intersects two
independent necessary relaxations of a square-order core:

* exact multiset consequences of the proved branch sizes and branch weights;
* aggregate edge counts between defect-graph incidence-weight classes.

UNSAT therefore rejects a profile, while SAT does not construct a graph.
"""

import z3

from square_order_branch_profile_census import (
    arithmetic_profiles,
    vertex_type_feasible,
)


def defect_weight_class_feasible(h, counts):
    solver = z3.Solver()
    edges = {}
    for i in range(5):
        for j in range(i, 5):
            edge_count = z3.Int(f"edges_{i}_{j}")
            edges[i, j] = edge_count
            solver.add(edge_count >= 0)
            maximum = (
                counts[i] * (counts[i] - 1) // 2
                if i == j
                else counts[i] * counts[j]
            )
            solver.add(edge_count <= maximum)

    for i in range(5):
        degree_incidence = 2 * edges[i, i] + sum(
            edges[min(i, j), max(i, j)] for j in range(5) if j != i
        )
        neighbor_weight = 2 * i * edges[i, i] + sum(
            j * edges[min(i, j), max(i, j)] for j in range(5) if j != i
        )
        # A low vertex of weight i has D-degree 7-i and its D-neighbor
        # weights sum to h-i, by (D+I)k=h1.
        solver.add(degree_incidence == counts[i] * (7 - i))
        solver.add(neighbor_weight == counts[i] * (h - i))

    return solver.check() == z3.sat


def high_overlap_feasible(h, counts):
    """Necessary consequence of k(u)+k(v) <= h+1 for distinct lows."""
    weights = [weight for weight, count in enumerate(counts) for _ in range(count)]
    return all(
        weights[i] + weights[j] <= h + 1
        for i in range(len(weights))
        for j in range(i + 1, len(weights))
    )


def main():
    profiles = arithmetic_profiles()
    overlap_survivors = [
        (h, counts) for h, counts in profiles if high_overlap_feasible(h, counts)
    ]
    branch_survivors = []
    for h, counts in profiles:
        if all(
            vertex_type_feasible(h, counts, k)
            for k, multiplicity in enumerate(counts)
            if multiplicity
        ):
            branch_survivors.append((h, counts))

    combined_survivors = []
    additionally_rejected = []
    for h, counts in branch_survivors:
        if defect_weight_class_feasible(h, counts):
            combined_survivors.append((h, counts))
        else:
            additionally_rejected.append((h, counts))

    expected = {2: 1, 4: 3, 6: 7, 8: 18, 10: 19, 12: 3}
    by_h = {
        h: sum(profile_h == h for profile_h, _ in combined_survivors)
        for h in expected
    }
    assert len(branch_survivors) == 52
    assert len(overlap_survivors) == 74
    assert {
        h: sum(profile_h == h for profile_h, _ in overlap_survivors)
        for h in expected
    } == {2: 1, 4: 3, 6: 10, 8: 29, 10: 22, 12: 9}
    assert len(combined_survivors) == 51
    assert by_h == expected
    assert additionally_rejected == [(12, (1, 0, 48, 0, 3))]

    print(f"high-overlap survivors: {len(overlap_survivors)}")
    print(f"branch-partition survivors: {len(branch_survivors)}")
    print(f"combined necessary-system survivors: {len(combined_survivors)} {by_h}")
    print("additional defect-class rejection:")
    for h, counts in additionally_rejected:
        print(f"h={h} low_counts={counts}")


if __name__ == "__main__":
    main()
