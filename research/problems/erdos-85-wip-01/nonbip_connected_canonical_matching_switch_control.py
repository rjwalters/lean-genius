#!/usr/bin/env python3
"""Falsify naive canonical switches in the signed Levi exchange graph."""

from __future__ import annotations

import networkx as nx

from binary_q4_fixed_free_disconnected_control import A_EDGES, N, adjacency


def first_matching(neighbors: list[set[int]]) -> tuple[int, ...]:
    def search(row: int, used: set[int], prefix: list[int]) -> tuple[int, ...] | None:
        if row == N:
            return tuple(prefix)
        for column in sorted(neighbors[row] - used):
            result = search(row + 1, used | {column}, prefix + [column])
            if result is not None:
                return result
        return None

    result = search(0, set(), [])
    assert result is not None
    return result


def even_cycles(
    matching: tuple[int, ...], neighbors: list[set[int]]
) -> list[tuple[int, ...]]:
    graph = nx.DiGraph()
    graph.add_nodes_from(range(N))
    graph.add_edges_from(
        (row, target)
        for row in range(N)
        for target in range(N)
        if row != target and matching[target] in neighbors[row]
    )
    result = []
    for cycle in nx.simple_cycles(graph):
        if len(cycle) < 4 or len(cycle) % 2:
            continue
        offset = cycle.index(min(cycle))
        result.append(tuple(cycle[offset:] + cycle[:offset]))
    return result


def switch(matching: tuple[int, ...], cycle: tuple[int, ...]) -> tuple[int, ...]:
    result = list(matching)
    for row, target in zip(cycle, cycle[1:] + cycle[:1]):
        result[row] = matching[target]
    return tuple(result)


def main() -> None:
    neighbors = adjacency(A_EDGES)
    matching = first_matching(neighbors)
    checks = []
    for name, key in (
        ("lexicographic", lambda cycle: cycle),
        ("shortest_then_lexicographic", lambda cycle: (len(cycle), cycle)),
    ):
        first_cycle = min(even_cycles(matching, neighbors), key=key)
        switched = switch(matching, first_cycle)
        second_cycle = min(even_cycles(switched, neighbors), key=key)
        restored = switch(switched, second_cycle)
        checks.append((name, first_cycle, second_cycle, restored == matching))
        assert restored != matching

    print(f"matching={matching}")
    for name, first_cycle, second_cycle, involutive in checks:
        print(f"{name}_first={first_cycle}")
        print(f"{name}_after_switch={second_cycle}")
        print(f"{name}_involutive={involutive}")


if __name__ == "__main__":
    main()
