#!/usr/bin/env python3
"""Verify the local q=6 marked-endpoint-cubic failure from audit Section 29."""

import numpy as np
from itertools import combinations


def cycle_adjacency(order: int, cycle: list[int]) -> np.ndarray:
    matrix = np.zeros((order, order), dtype=np.uint8)
    for left, right in zip(cycle, cycle[1:] + cycle[:1]):
        matrix[left, right] = 1
        matrix[right, left] = 1
    return matrix


def main() -> None:
    order = 12
    components = [list(range(5)), list(range(5, 12))]

    shadow = np.zeros((order, order), dtype=np.uint8)
    cross = np.zeros((order, order), dtype=np.uint8)
    for component in components:
        for index, vertex in enumerate(component):
            successor = component[(index + 1) % len(component)]
            shadow[vertex, successor] = shadow[successor, vertex] = 1
            cross[vertex, vertex] = 1
            cross[vertex, successor] = 1

    source_internal = shadow.copy()
    target_cycle = [5, 8, 3, 10, 0, 6, 2, 11, 7, 1, 9, 4]
    target_internal = cycle_adjacency(order, target_cycle)
    graph = np.block(
        [[source_internal, cross], [cross.T, target_internal]]
    )

    assert np.all(graph == graph.T)
    assert np.all(np.diag(graph) == 0)
    assert np.all(graph.sum(axis=1) == 4)
    common = graph @ graph
    assert max(
        int(common[left, right])
        for left in range(2 * order)
        for right in range(left + 1, 2 * order)
    ) == 1

    assert np.all(cross.sum(axis=0) == 2)
    assert np.all(cross.sum(axis=1) == 2)
    assert np.array_equal((cross.T @ cross) % 2, shadow)
    assert np.array_equal((cross @ cross.T) % 2, shadow)

    first_component = np.zeros(order, dtype=np.uint8)
    first_component[components[0]] = 1
    assert np.all((shadow @ first_component) % 2 == 0)

    marked_cubic = (
        shadow @ ((shadow + target_internal) @ (target_internal @ first_component))
    ) % 2
    assert marked_cubic[components[0]].tolist() == [0, 1, 0, 0, 1]

    source_routes = source_internal @ cross
    target_routes = cross @ target_internal
    assert np.all(source_routes <= 1)
    assert np.all(target_routes <= 1)
    assert not np.any(source_routes * target_routes)
    residual = np.ones((order, order), dtype=np.uint8) - source_routes - target_routes
    assert np.all(residual.sum(axis=0) == 4)
    assert np.all(residual.sum(axis=1) == 4)

    rectangles: set[tuple[int, int]] = set()
    for source_pair in combinations(range(order), 2):
        for target_pair in combinations(range(order), 2):
            if all(residual[source, target] for source in source_pair for target in target_pair):
                rectangles.update(
                    (source, target)
                    for source in source_pair
                    for target in target_pair
                )
    assert residual[0, 3] == 1
    assert (0, 3) not in rectangles

    print("verified: local q=6 two-shore graph is 4-regular and C4-free")
    print("cross-shadow components: C5 and C7; source internal factor matches shadow")
    print("marked cubic on C5 ports:", marked_cubic[components[0]].tolist())
    print("SRP extension obstruction: residual edge (0,3) lies in no K2,2")


if __name__ == "__main__":
    main()
