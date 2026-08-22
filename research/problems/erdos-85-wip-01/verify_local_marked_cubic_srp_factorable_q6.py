#!/usr/bin/env python3
"""Verify a q=6 pairwise-SRP-factorable marked-cubic failure."""

import numpy as np


def cycle_adjacency(order: int, cycle: list[int]) -> np.ndarray:
    matrix = np.zeros((order, order), dtype=np.uint8)
    for left, right in zip(cycle, cycle[1:] + cycle[:1]):
        matrix[left, right] = matrix[right, left] = 1
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
            cross[vertex, vertex] = cross[vertex, successor] = 1

    target_cycle = [11, 3, 7, 10, 1, 5, 9, 4, 6, 2, 8, 0]
    target_internal = cycle_adjacency(order, target_cycle)
    graph = np.block([[shadow, cross], [cross.T, target_internal]])
    common = graph @ graph
    assert np.all(graph.sum(axis=1) == 4)
    assert max(
        int(common[left, right])
        for left in range(2 * order)
        for right in range(left + 1, 2 * order)
    ) == 1

    residual = np.ones((order, order), dtype=np.uint8) - shadow @ cross - cross @ target_internal
    rectangles = [
        ((0, 1), (7, 9)),
        ((0, 8), (3, 6)),
        ((1, 7), (4, 11)),
        ((2, 4), (5, 10)),
        ((2, 6), (0, 9)),
        ((3, 5), (8, 10)),
        ((3, 7), (1, 5)),
        ((4, 11), (2, 7)),
        ((5, 9), (0, 3)),
        ((6, 8), (1, 11)),
        ((9, 10), (2, 6)),
        ((10, 11), (4, 8)),
    ]
    source_to_third = np.zeros((order, order), dtype=np.uint8)
    third_to_target = np.zeros((order, order), dtype=np.uint8)
    for third, (source_pair, target_pair) in enumerate(rectangles):
        source_to_third[list(source_pair), third] = 1
        third_to_target[third, list(target_pair)] = 1

    assert np.all(source_to_third.sum(axis=0) == 2)
    assert np.all(source_to_third.sum(axis=1) == 2)
    assert np.all(third_to_target.sum(axis=0) == 2)
    assert np.all(third_to_target.sum(axis=1) == 2)
    assert np.array_equal(source_to_third @ third_to_target, residual)

    first_component = np.zeros(order, dtype=np.uint8)
    first_component[components[0]] = 1
    marked_cubic = (
        shadow @ ((shadow + target_internal) @ (target_internal @ first_component))
    ) % 2
    assert marked_cubic[components[0]].tolist() == [1, 0, 1, 1, 1]

    print("verified: q=6 local model is 4-regular and C4-free")
    print("verified: endpoint residual factors through one degree-two third shore")
    print("marked cubic on C5 ports:", marked_cubic[components[0]].tolist())


if __name__ == "__main__":
    main()
