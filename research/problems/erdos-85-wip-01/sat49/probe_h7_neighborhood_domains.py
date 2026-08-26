#!/usr/bin/env python3
"""Measure complete-row domains for an H7 exact-cover reformulation."""

from __future__ import annotations

import argparse
import itertools
import json
import math

import check_h7_t0_by_empty_graph as cubes


PAIRS = tuple(itertools.combinations(range(7), 2))
PAIR_VERTEX = {pair: 21 + index for index, pair in enumerate(PAIRS)}
SINGLETON_VERTEX = {(label, copy): 7 + 2 * label + copy
                    for label in range(7) for copy in range(2)}
SUPPORT = ([0] * 7 + [1 << label for label in range(7) for _ in range(2)] +
           [(1 << left) | (1 << right) for left, right in PAIRS])


def disjoint_pair_sets(size: int) -> list[tuple[tuple[int, int], ...]]:
    result = []
    for selected in itertools.combinations(PAIRS, size):
        support = 0
        for left, right in selected:
            support |= (1 << left) | (1 << right)
        if support.bit_count() == 2 * size:
            result.append(selected)
    return result


PAIR_SETS = {size: disjoint_pair_sets(size) for size in range(4)}


def row_domains(vertex: int, empty_mask: int) -> list[int]:
    """Return bitsets for all rows satisfying degree, BC=J, and E-E pins."""
    residual_degree = 7 - SUPPORT[vertex].bit_count()
    fixed_empty = []
    if vertex < 7:
        fixed_empty = [
            other for other in range(7) if other != vertex and
            (empty_mask >> cubes.quotient.EDGE_INDEX[
                tuple(sorted((vertex, other)))]) & 1
        ]
    result = []
    for pair_count in range(4):
        singleton_count = 7 - 2 * pair_count
        empty_count = residual_degree - pair_count - singleton_count
        if (not 0 <= empty_count <= 7 or
                (vertex < 7 and empty_count != len(fixed_empty))):
            continue
        for selected_pairs in PAIR_SETS[pair_count]:
            pair_vertices = [PAIR_VERTEX[pair] for pair in selected_pairs]
            if vertex in pair_vertices:
                continue
            used_labels = {label for pair in selected_pairs for label in pair}
            singleton_options = [
                [SINGLETON_VERTEX[label, copy] for copy in range(2)
                 if SINGLETON_VERTEX[label, copy] != vertex]
                for label in range(7) if label not in used_labels
            ]
            empty_options = ([tuple(fixed_empty)] if vertex < 7 else
                             list(itertools.combinations(range(7), empty_count)))
            for singletons in itertools.product(*singleton_options):
                for empties in empty_options:
                    bitset = 0
                    for neighbor in (*pair_vertices, *singletons, *empties):
                        bitset |= 1 << neighbor
                    result.append(bitset)
    return result


def forward_counts(root: int, root_row: int,
                   domains: list[list[int]]) -> list[int]:
    """Filter every other row by symmetry and the full common-neighbor cap."""
    result = []
    for vertex, candidates in enumerate(domains):
        if vertex == root:
            continue
        adjacent = (root_row >> vertex) & 1
        fixed_common = (SUPPORT[root] & SUPPORT[vertex]).bit_count()
        result.append(sum(
            ((candidate >> root) & 1) == adjacent and
            fixed_common + (root_row & candidate).bit_count() <= 1
            for candidate in candidates
        ))
    return result


def probe(edge_count: int, type_index: int) -> dict:
    representatives = cubes.graph_representatives(edge_count)
    if not 0 <= type_index < len(representatives):
        raise ValueError("type index is outside the canonical inventory")
    mask = representatives[type_index]
    domains = [row_domains(vertex, mask) for vertex in range(42)]
    root = min(range(42), key=lambda vertex: len(domains[vertex]))
    forward = [forward_counts(root, row, domains) for row in domains[root]]
    survivors = [counts for counts in forward if all(counts)]
    return {
        "edge_count": edge_count,
        "type_index": type_index,
        "empty_mask": mask,
        "domain_counts": [len(rows) for rows in domains],
        "domain_total": sum(map(len, domains)),
        "unconditioned_log10_product": sum(math.log10(len(rows)) for rows in domains),
        "root": root,
        "root_choices": len(domains[root]),
        "root_choices_surviving_forward_check": len(survivors),
        "best_forward_log10_product": min(
            sum(math.log10(count) for count in counts) for counts in survivors),
        "best_forward_domain_total": min(sum(counts) for counts in survivors),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--edge-count", type=int, choices=range(6, 10), required=True)
    parser.add_argument("--type-index", type=int, required=True)
    args = parser.parse_args()
    print(json.dumps(probe(args.edge_count, args.type_index), sort_keys=True))


if __name__ == "__main__":
    main()
