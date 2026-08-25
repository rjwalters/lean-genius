#!/usr/bin/env python3
"""Refute the direct Hajnal--Szemeredi gate for compensated surgery.

For a delete-``k``/add-``k+1`` repair, make one occurrence of an old vertex
for each lost incident edge.  Join two occurrences when they represent the
same old vertex, or when their old vertices have a common neighbor in the
survivor graph.  A proper equitable ``(k+1)``-coloring is exactly a balanced
compatible-selector allocation (for an edgeless new gadget).

The Hajnal--Szemeredi theorem would supply that coloring from
``maximum_degree <= k``.  This bounded probe reconstructs the already
verified positive ``d=4`` repairs and checks that this sufficient condition
fails on every one: maximum degrees are 3 for ``k=1`` and 6 for the standard
edgeless ``k=2`` repair.  The selectors themselves still give the required
equitable colorings.  Hence the global-repartition problem is real, but its
solution cannot be obtained by the raw maximum-degree gate.
"""

from collections import Counter
from pathlib import Path
import sys


HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import compensated_surgery_control as k1_control  # noqa: E402
import compensated_surgery_k2_control as k2_control  # noqa: E402


Occurrence = tuple[int, int]


def occurrence_conflict_graph(deleted, attachments, removed):
    deleted_set = set(deleted if isinstance(deleted, tuple) else (deleted,))
    old = [vertex for vertex in range(15) if vertex not in deleted_set]
    removed_set = set(removed)
    survivor_edges = {
        edge
        for edge in k1_control.EDGES
        if not deleted_set.intersection(edge) and edge not in removed_set
    }

    if isinstance(attachments, list):
        selector_items = tuple(enumerate(attachments))
    else:
        selector_items = tuple(sorted(attachments.items()))

    occurrences = tuple(
        (vertex, color)
        for color, selector in selector_items
        for vertex in selector
    )
    adjacency = {occurrence: set() for occurrence in occurrences}

    def survivor_adjacent(left: int, right: int) -> bool:
        return tuple(sorted((left, right))) in survivor_edges

    for index, left_occurrence in enumerate(occurrences):
        left, _ = left_occurrence
        for right_occurrence in occurrences[index + 1 :]:
            right, _ = right_occurrence
            conflict = left == right or any(
                witness not in (left, right)
                and survivor_adjacent(left, witness)
                and survivor_adjacent(right, witness)
                for witness in old
            )
            if conflict:
                adjacency[left_occurrence].add(right_occurrence)
                adjacency[right_occurrence].add(left_occurrence)
    return selector_items, adjacency


def verify_coloring(selector_items, adjacency, selector_size: int) -> None:
    color_sizes = Counter()
    for occurrence, neighbors in adjacency.items():
        _, color = occurrence
        color_sizes[color] += 1
        assert all(neighbor[1] != color for neighbor in neighbors)
    assert set(color_sizes.values()) == {selector_size}
    assert set(color_sizes) == {color for color, _ in selector_items}


def main() -> None:
    k1_result = k1_control.solve("compensated")
    assert k1_result is not None
    deleted, gadget_edge, attachments, removed = k1_result
    assert not gadget_edge
    selectors, adjacency = occurrence_conflict_graph(
        deleted, attachments, removed
    )
    verify_coloring(selectors, adjacency, selector_size=4)
    k1_maximum_degree = max(map(len, adjacency.values()))
    assert k1_maximum_degree == 3 > 1
    print(f"k=1: equitable 2-coloring exists; occurrence max degree={k1_maximum_degree}")

    k2_result = k2_control.solve(
        gadget_edges=0, require_common_root=True
    )
    assert k2_result is not None
    deleted, _, attachments, removed = k2_result
    selectors, adjacency = occurrence_conflict_graph(
        deleted, attachments, removed
    )
    verify_coloring(selectors, adjacency, selector_size=4)
    k2_maximum_degree = max(map(len, adjacency.values()))
    assert k2_maximum_degree == 6 > 2
    print(f"k=2: equitable 3-coloring exists; occurrence max degree={k2_maximum_degree}")

    print("raw Hajnal--Szemeredi maximum-degree gate: REFUTED")


if __name__ == "__main__":
    main()
