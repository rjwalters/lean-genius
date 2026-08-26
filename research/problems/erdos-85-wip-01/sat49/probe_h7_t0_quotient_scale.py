#!/usr/bin/env python3
"""Count H7/T0 empty-sector graph types before a completion census.

This is a scale probe, not a contradiction checker.  It enumerates every
labeled seven-vertex empty-sector graph with 6--10 edges that passes the
proved maximum-degree-three and common-neighbor filters, then quotients those
graphs by all permutations of the seven high labels.  For each resulting
unlabeled graph type it optionally runs the existing bounded copy-indexed
quotient search once.

The quotient search's ``None`` result is deliberately reported as
``no_answer_within_budget``: its current API does not distinguish exhaustive
failure from exhausting the per-graph node budget.
"""

from __future__ import annotations

import argparse
import itertools
from collections import Counter

import check_h7_t0_copy_quotient as quotient


PERMUTATIONS = tuple(itertools.permutations(quotient.VERTICES))


def edge_mask(edge_indices: tuple[int, ...]) -> int:
    return sum(1 << index for index in edge_indices)


def permuted_mask(mask: int, permutation: tuple[int, ...]) -> int:
    result = 0
    while mask:
        bit = mask & -mask
        mask -= bit
        left, right = quotient.EDGES[bit.bit_length() - 1]
        edge = tuple(sorted((permutation[left], permutation[right])))
        result |= 1 << quotient.EDGE_INDEX[edge]
    return result


def orbit(mask: int) -> set[int]:
    return {permuted_mask(mask, permutation) for permutation in PERMUTATIONS}


def graph_data(mask: int) -> tuple[tuple[int, ...], tuple[int, ...]]:
    indices = tuple(index for index in range(21) if (mask >> index) & 1)
    adjacency = quotient.adjacency_of_edges(indices)
    degrees = tuple(neighbors.bit_count() for neighbors in adjacency)
    return adjacency, degrees


def probe(edge_count: int, node_budget: int, run_assignments: bool) -> Counter:
    counts = Counter()
    seen: set[int] = set()
    for indices in itertools.combinations(range(21), edge_count):
        mask = edge_mask(indices)
        if mask in seen:
            continue
        adjacency, degrees = graph_data(mask)
        if not quotient.passes_graph_filters(adjacency, degrees):
            continue
        masks = orbit(mask)
        seen.update(masks)
        counts["unlabeled_graph_types"] += 1
        counts["labeled_graphs"] += len(masks)
        if run_assignments:
            assignment = quotient.compatible_assignment(
                adjacency, degrees, node_budget=node_budget
            )
            if assignment is None:
                counts["no_answer_within_budget"] += 1
            else:
                quotient.validate_assignment(adjacency, degrees, assignment)
                counts["sat_relaxation_graph_types"] += 1
    return counts


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--node-budget", type=int, default=5000)
    parser.add_argument("--skip-assignments", action="store_true")
    args = parser.parse_args()
    print(f"node_budget={args.node_budget}")
    print(f"assignments={'off' if args.skip_assignments else 'on'}")
    for edge_count in range(6, 11):
        counts = probe(
            edge_count,
            node_budget=args.node_budget,
            run_assignments=not args.skip_assignments,
        )
        print(f"F={edge_count} {dict(sorted(counts.items()))}")


if __name__ == "__main__":
    main()
