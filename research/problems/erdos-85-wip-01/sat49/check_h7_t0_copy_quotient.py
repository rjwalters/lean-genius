#!/usr/bin/env python3
"""Search the sound copy-indexed H7/T0 local quotient relaxation.

This checker deliberately models only constraints already proved in Lean:

* the seven empty-support vertices induce a graph of maximum degree three
  with at most one common empty neighbor per pair;
* an empty vertex of empty-degree ``d`` partitions the seven high labels into
  ``d`` pair labels and ``7-2d`` singleton labels;
* each singleton incidence chooses one of TWO ACTUAL copies of its label;
* each actual singleton copy is used by at most two empty vertices;
* distinct empty vertices never reuse the same pair-support vertex;
* two empty vertices share at most one actual singleton copy, and none when
  they already share an empty neighbor.

The graph-facing quotient formulas force 6 <= |EE| <= 10.  A SAT result is a
witness that these necessary local constraints do not by themselves give a
contradiction.  An UNSAT result would still be discovery evidence only and
would require rule-by-rule ablation and a Lean finite bridge.  The model is a
RELAXATION: it does not yet construct the singleton-singleton and pair-sector
edges required by their own full degree profiles, so SAT must not be mistaken
for a graph witness.
"""

from __future__ import annotations

import itertools
from dataclasses import dataclass
from functools import lru_cache


VERTICES = tuple(range(7))
EDGES = tuple(itertools.combinations(VERTICES, 2))
EDGE_INDEX = {edge: index for index, edge in enumerate(EDGES)}


def perfect_matchings(vertices: tuple[int, ...]):
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
    """Options ``(actual-singleton mask, pair-label mask)`` by E-degree."""
    result = {}
    for degree in range(4):
        options = []
        singleton_count = 7 - 2 * degree
        for labels in itertools.combinations(VERTICES, singleton_count):
            label_mask = sum(1 << label for label in labels)
            complement = tuple(
                label for label in VERTICES if not (label_mask >> label) & 1
            )
            for copy_bits in range(1 << singleton_count):
                actual_mask = 0
                for position, label in enumerate(labels):
                    copy = (copy_bits >> position) & 1
                    actual_mask |= 1 << (2 * label + copy)
                for matching in perfect_matchings(complement):
                    options.append((actual_mask, matching))
        result[degree] = tuple(options)
    return result


OPTIONS = quotient_options()


@lru_cache(maxsize=None)
def compatibility_row(
    left_degree: int,
    right_degree: int,
    already_common: bool,
    left_index: int,
) -> int:
    left_singletons, left_pairs = OPTIONS[left_degree][left_index]
    compatible = 0
    for index, (right_singletons, right_pairs) in enumerate(
        OPTIONS[right_degree]
    ):
        shared_actual = (left_singletons & right_singletons).bit_count()
        if shared_actual + int(already_common) <= 1 and not (
            left_pairs & right_pairs
        ):
            compatible |= 1 << index
    return compatible


def adjacency_of_edges(edge_indices: tuple[int, ...]) -> tuple[int, ...]:
    adjacency = [0] * 7
    for edge_index in edge_indices:
        left, right = EDGES[edge_index]
        adjacency[left] |= 1 << right
        adjacency[right] |= 1 << left
    return tuple(adjacency)


def passes_graph_filters(adjacency: tuple[int, ...], degrees: tuple[int, ...]):
    return max(degrees) <= 3 and all(
        (adjacency[left] & adjacency[right]).bit_count() <= 1
        for left in VERTICES
        for right in range(left + 1, 7)
    )


def capacity_ok(actual_mask: int, usage: tuple[int, ...]) -> bool:
    while actual_mask:
        bit = actual_mask & -actual_mask
        actual_mask -= bit
        if usage[bit.bit_length() - 1] >= 2:
            return False
    return True


def add_usage(actual_mask: int, usage: tuple[int, ...]) -> tuple[int, ...]:
    updated = list(usage)
    while actual_mask:
        bit = actual_mask & -actual_mask
        actual_mask -= bit
        updated[bit.bit_length() - 1] += 1
    return tuple(updated)


def compatible_assignment(
    adjacency: tuple[int, ...], degrees: tuple[int, ...], node_budget: int = 5000
) -> tuple[int, ...] | None:
    """Return one option index per empty vertex, or ``None``."""
    first = max(VERTICES, key=lambda vertex: degrees[vertex])
    first_degree = degrees[first]

    # S7 on labels, together with independent swaps of the two actual copies
    # for each label, is transitive on options of a fixed empty-degree.
    first_option = 0
    assignment = {first: first_option}
    first_actual = OPTIONS[first_degree][first_option][0]
    usage = add_usage(first_actual, (0,) * 14)
    domains = {
        vertex: (1 << len(OPTIONS[degrees[vertex]])) - 1
        for vertex in VERTICES
        if vertex != first
    }
    for vertex in domains:
        domains[vertex] &= compatibility_row(
            first_degree,
            degrees[vertex],
            bool(adjacency[first] & adjacency[vertex]),
            first_option,
        )

    nodes = 0

    def search(
        current_domains: dict[int, int],
        current_usage: tuple[int, ...],
        current_assignment: dict[int, int],
    ) -> tuple[int, ...] | None:
        nonlocal nodes
        nodes += 1
        if nodes > node_budget:
            return None
        if not current_domains:
            return tuple(current_assignment[v] for v in VERTICES)
        vertex = min(
            current_domains,
            key=lambda candidate: current_domains[candidate].bit_count(),
        )
        choices_mask = current_domains[vertex]
        degree = degrees[vertex]
        choices = []
        while choices_mask:
            choice = choices_mask & -choices_mask
            choices_mask -= choice
            option = choice.bit_length() - 1
            actual_mask = OPTIONS[degree][option][0]
            if not capacity_ok(actual_mask, current_usage):
                continue
            pressure = sum(
                current_usage[i] for i in range(14) if (actual_mask >> i) & 1
            )
            choices.append((pressure, option, actual_mask))
        for _pressure, option, actual_mask in sorted(choices):
            next_domains = {}
            for other, domain in current_domains.items():
                if other == vertex:
                    continue
                restricted = domain & compatibility_row(
                    degree,
                    degrees[other],
                    bool(adjacency[vertex] & adjacency[other]),
                    option,
                )
                if not restricted:
                    break
                next_domains[other] = restricted
            else:
                current_assignment[vertex] = option
                answer = search(
                    next_domains,
                    add_usage(actual_mask, current_usage),
                    current_assignment,
                )
                if answer is not None:
                    return answer
                del current_assignment[vertex]
        return None

    return search(domains, usage, assignment)


@dataclass(frozen=True)
class SearchResult:
    tested_graphs: int
    filtered_graphs: int
    edge_count: int
    edge_indices: tuple[int, ...] | None
    assignment: tuple[int, ...] | None


def validate_assignment(
    adjacency: tuple[int, ...],
    degrees: tuple[int, ...],
    assignment: tuple[int, ...],
) -> None:
    """Independent assertions for every modeled rule on a returned witness."""
    assert passes_graph_filters(adjacency, degrees)
    assert len(assignment) == 7
    usage = [0] * 14
    for vertex, option_index in enumerate(assignment):
        actual, _pairs = OPTIONS[degrees[vertex]][option_index]
        assert actual.bit_count() == 7 - 2 * degrees[vertex]
        for copy in range(14):
            usage[copy] += (actual >> copy) & 1
    assert max(usage) <= 2
    for left in VERTICES:
        left_actual, left_pairs = OPTIONS[degrees[left]][assignment[left]]
        for right in range(left + 1, 7):
            right_actual, right_pairs = OPTIONS[degrees[right]][assignment[right]]
            already_common = bool(adjacency[left] & adjacency[right])
            assert (left_actual & right_actual).bit_count() + int(
                already_common
            ) <= 1
            assert not (left_pairs & right_pairs)

    # Check the graph-global directed quotient equations now formalized in
    # `sevenHigh_t0_directed_quotient_one_parameter`.  The relaxation
    # constructs only E-E, E-S, and E-P incidences; the remaining values below
    # are completion targets, not constructed P-P/P-S/S-S edge sets.
    directed_d = sum(degrees)
    pair_to_empty = sum(degrees)
    singleton_to_empty = sum(7 - 2 * degree for degree in degrees)
    assert pair_to_empty == directed_d
    assert singleton_to_empty + 2 * directed_d == 49
    assert directed_d + 42 >= 0  # I22 target
    assert 63 - 2 * directed_d >= 0  # I21 target
    assert 4 * directed_d - 28 >= 0  # I11 target
    assert 11 <= directed_d <= 21


def run_search() -> SearchResult:
    tested = 0
    filtered = 0
    # F=7 has many quotient graphs and was the first SAT stratum after
    # ablating the old unsound label rule.  Search it first, then the others.
    for edge_count in (7, 8, 6, 9, 10):
        for edge_indices in itertools.combinations(range(len(EDGES)), edge_count):
            tested += 1
            adjacency = adjacency_of_edges(edge_indices)
            degrees = tuple(neighbors.bit_count() for neighbors in adjacency)
            if not passes_graph_filters(adjacency, degrees):
                continue
            filtered += 1
            assignment = compatible_assignment(adjacency, degrees)
            if assignment is not None:
                validate_assignment(adjacency, degrees, assignment)
                return SearchResult(
                    tested, filtered, edge_count, edge_indices, assignment
                )
    return SearchResult(tested, filtered, -1, None, None)


def main() -> None:
    result = run_search()
    print(f"tested_graphs={result.tested_graphs}")
    print(f"filtered_graphs={result.filtered_graphs}")
    if result.assignment is None:
        print("verdict=NO_SAT_FOUND_WITHIN_PER_GRAPH_NODE_BUDGET")
        return
    print("verdict=SAT_RELAXATION")
    print(f"edge_count={result.edge_count}")
    print(f"edge_indices={result.edge_indices}")
    print(f"edges={tuple(EDGES[i] for i in result.edge_indices or ())}")
    print(f"option_indices={result.assignment}")
    directed_d = 2 * result.edge_count
    print(
        "directed_targets="
        + repr(
            {
                "I00=I20=I02": directed_d,
                "I22": directed_d + 42,
                "I01=I10": 49 - 2 * directed_d,
                "I21": 63 - 2 * directed_d,
                "I11": 4 * directed_d - 28,
            }
        )
    )
    for vertex, option_index in enumerate(result.assignment):
        degree = sum(vertex in edge for edge in tuple(
            EDGES[i] for i in result.edge_indices or ()
        ))
        actual, pairs = OPTIONS[degree][option_index]
        copies = tuple(i for i in range(14) if (actual >> i) & 1)
        pair_labels = tuple(EDGES[i] for i in range(21) if (pairs >> i) & 1)
        print(f"v{vertex}: degree={degree} copies={copies} pairs={pair_labels}")


if __name__ == "__main__":
    main()
