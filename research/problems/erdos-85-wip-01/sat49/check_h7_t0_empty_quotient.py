#!/usr/bin/env python3
"""Exhaust the empty-support quotient forced by the H7 T0 profile.

For a hypothetical order-49 witness with seven high vertices and no
triple-support low vertex, write P/S/E for low vertices whose high support
has size 2/1/0.  Exact-one neighborhood partitions imply, for every low y,

    #P-neighbors(y) - #E-neighbors(y) = |support(y)|.

Consequently the six low-edge class counts are determined by F = |E(E)|:

    PP=21+F, PS=63-4F, PE=2F,
    SS=4F-14, SE=49-4F, EE=F,

and 4 <= F <= 10.  If an empty vertex has empty-degree d, its remaining
neighbors label a partition of the seven high points into d disjoint pairs
and 7-2d singletons.  C4-freeness imposes three small compatibility rules:

* the graph induced by the seven empty vertices has at most one common
  neighbor per vertex pair;
* two singleton-label sets intersect in at most one point, and are disjoint
  when their empty vertices already have a common empty neighbor;
* pair labels used at distinct empty vertices are disjoint, since a
  pair-support vertex has at most one empty neighbor.

This program checks every labeled seven-vertex empty graph with 4..10 edges
and every compatible label partition.  It is a reproducible discovery
checker for the structural contradiction; the graph-to-quotient derivation
still belongs in Lean before this can replace the H7 LRAT campaign.
"""

from __future__ import annotations

import argparse
import itertools
from dataclasses import dataclass


VERTICES = tuple(range(7))
EDGES = tuple(itertools.combinations(VERTICES, 2))
EDGE_INDEX = {edge: index for index, edge in enumerate(EDGES)}


def perfect_matchings(vertices: tuple[int, ...]):
    """Yield edge-bitmasks for all perfect matchings of ``vertices``."""
    if not vertices:
        yield 0
        return
    first = vertices[0]
    for index, second in enumerate(vertices[1:], 1):
        edge = 1 << EDGE_INDEX[tuple(sorted((first, second)))]
        remaining = vertices[1:index] + vertices[index + 1:]
        for matching in perfect_matchings(remaining):
            yield matching | edge


def quotient_options() -> dict[int, tuple[tuple[int, int], ...]]:
    """Options ``(singleton-label mask, pair-label mask)`` by empty-degree."""
    result = {}
    for degree in range(4):
        options = []
        singleton_count = 7 - 2 * degree
        for labels in itertools.combinations(VERTICES, singleton_count):
            singleton_mask = sum(1 << label for label in labels)
            complement = tuple(
                label for label in VERTICES
                if not (singleton_mask >> label) & 1
            )
            options.extend(
                (singleton_mask, matching)
                for matching in perfect_matchings(complement)
            )
        result[degree] = tuple(options)
    return result


OPTIONS = quotient_options()


def compatibility_tables():
    """Bitset compatibility rows indexed by degrees and common-neighbor bit."""
    tables = {}
    for left_degree, left_options in OPTIONS.items():
        for right_degree, right_options in OPTIONS.items():
            for already_common in (False, True):
                rows = []
                for left_singletons, left_pairs in left_options:
                    compatible = 0
                    for index, (right_singletons, right_pairs) in enumerate(
                            right_options):
                        intersection = (
                            left_singletons & right_singletons
                        ).bit_count()
                        singleton_ok = (
                            intersection == 0 if already_common
                            else intersection <= 1
                        )
                        if singleton_ok and not (left_pairs & right_pairs):
                            compatible |= 1 << index
                    rows.append(compatible)
                tables[left_degree, right_degree, already_common] = tuple(rows)
    return tables


COMPATIBILITY = compatibility_tables()


@dataclass(frozen=True)
class SearchResult:
    tested_graphs: int
    filtered_graphs: int
    filtered_by_edges: dict[int, int]
    satisfiable: bool


def has_compatible_labels(adjacency: tuple[int, ...], degrees: tuple[int, ...]):
    """MRV bitset search for compatible label partitions on one empty graph."""
    first = max(VERTICES, key=lambda vertex: degrees[vertex])
    first_degree = degrees[first]

    # The symmetric group on the seven high labels acts transitively on the
    # options of each fixed degree, so option zero is without loss of
    # generality for the first empty vertex.
    first_option = 0
    domains = {
        vertex: (1 << len(OPTIONS[degrees[vertex]])) - 1
        for vertex in VERTICES if vertex != first
    }
    for vertex in domains:
        already_common = bool(adjacency[first] & adjacency[vertex])
        domains[vertex] &= COMPATIBILITY[
            first_degree, degrees[vertex], already_common
        ][first_option]

    def search(current_domains: dict[int, int]) -> bool:
        if not current_domains:
            return True
        vertex = min(
            current_domains,
            key=lambda candidate: current_domains[candidate].bit_count(),
        )
        choices = current_domains[vertex]
        while choices:
            choice = choices & -choices
            choices -= choice
            option = choice.bit_length() - 1
            next_domains = {}
            consistent = True
            for other, domain in current_domains.items():
                if other == vertex:
                    continue
                already_common = bool(adjacency[vertex] & adjacency[other])
                restricted = domain & COMPATIBILITY[
                    degrees[vertex], degrees[other], already_common
                ][option]
                if not restricted:
                    consistent = False
                    break
                next_domains[other] = restricted
            if consistent and search(next_domains):
                return True
        return False

    return search(domains)


def adjacency_of_edges(edge_indices: tuple[int, ...]) -> tuple[int, ...]:
    adjacency = [0] * 7
    for edge_index in edge_indices:
        left, right = EDGES[edge_index]
        adjacency[left] |= 1 << right
        adjacency[right] |= 1 << left
    return tuple(adjacency)


def passes_quotient_filters(adjacency: tuple[int, ...], degrees: tuple[int, ...]):
    if max(degrees) > 3:
        return False
    if any(
        (adjacency[left] & adjacency[right]).bit_count() > 1
        for left in VERTICES for right in range(left + 1, 7)
    ):
        return False
    # Each singleton-label pair may occur at only one empty vertex.
    singleton_pair_mass = sum(
        (7 - 2 * degree) * (6 - 2 * degree) // 2
        for degree in degrees
    )
    return singleton_pair_mass <= len(EDGES)


def run_search() -> SearchResult:
    tested = 0
    filtered = 0
    filtered_by_edges = {}
    for edge_count in range(4, 11):
        kept_at_count = 0
        for edge_indices in itertools.combinations(range(len(EDGES)), edge_count):
            tested += 1
            adjacency = adjacency_of_edges(edge_indices)
            degrees = tuple(neighbors.bit_count() for neighbors in adjacency)
            if not passes_quotient_filters(adjacency, degrees):
                continue
            filtered += 1
            kept_at_count += 1
            if has_compatible_labels(adjacency, degrees):
                return SearchResult(
                    tested, filtered, dict(filtered_by_edges), True
                )
        filtered_by_edges[edge_count] = kept_at_count
    return SearchResult(tested, filtered, filtered_by_edges, False)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.parse_args()
    result = run_search()
    print(f"tested_graphs={result.tested_graphs}")
    print(f"filtered_graphs={result.filtered_graphs}")
    print(f"filtered_by_edges={result.filtered_by_edges}")
    print("verdict=" + ("SAT" if result.satisfiable else "UNSAT"))
    if result.satisfiable:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
