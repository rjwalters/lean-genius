#!/usr/bin/env python3
"""Verify the explicit q=10 single-pair odd-holonomy model.

This is a local two-component diagnostic, not an ambient square-order graph
and not a realization of the five simultaneous routing colors.
"""


SIZES = (9, 11)
SHORE = sum(SIZES)


def edge(x: int, y: int) -> tuple[int, int]:
    return (x, y) if x < y else (y, x)


def adjacency(edges: set[tuple[int, int]]) -> list[set[int]]:
    neighbors = [set() for _ in range(2 * SHORE)]
    for x, y in edges:
        neighbors[x].add(y)
        neighbors[y].add(x)
    return neighbors


def main() -> None:
    source: set[tuple[int, int]] = set()
    target: set[tuple[int, int]] = set()
    cross: set[tuple[int, int]] = set()
    source_shadow: set[tuple[int, int]] = set()
    target_shadow: set[tuple[int, int]] = set()

    offset = 0
    for size in SIZES:
        source_step, target_step = (1, 3) if size == 9 else (3, 1)
        for i in range(size):
            left = offset + i
            right = SHORE + offset + i
            source.add(edge(left, offset + (i + source_step) % size))
            target.add(edge(right, SHORE + offset + (i + target_step) % size))
            cross.add(edge(right, offset + i))
            cross.add(edge(right, offset + (i + 1) % size))
            source_shadow.add(edge(left, offset + (i + 1) % size))
            target_shadow.add(edge(right, SHORE + offset + (i + 1) % size))
        offset += size

    graph = adjacency(source | target | cross)
    assert all(len(graph[x]) == 4 for x in range(2 * SHORE))
    assert max(
        len(graph[x] & graph[y])
        for x in range(2 * SHORE)
        for y in range(x + 1, 2 * SHORE)
    ) == 1

    p_source_target = len(source & source_shadow)
    p_target_source = len(target & target_shadow)
    assert (p_source_target, p_target_source) == (9, 11)
    assert p_source_target + p_target_source == 2 * 10

    source_owner = adjacency(source & source_shadow)
    target_owner = adjacency(target & target_shadow)
    for x in range(SHORE):
        ports = graph[x] & set(range(SHORE, 2 * SHORE))
        assert len(ports) == 2
        a = len(source_owner[x])
        b = int(edge(*ports) in target)
        assert a + 2 * b == 2
    for x in range(SHORE, 2 * SHORE):
        ports = graph[x] & set(range(SHORE))
        assert len(ports) == 2
        a = len(target_owner[x])
        b = int(edge(*ports) in source)
        assert a + 2 * b == 2

    print("verified: local q=10 pair is 4-regular and C4-free")
    print("owner intersections: p_ce=9, p_ec=11; odd horizontal C9 and C11")


if __name__ == "__main__":
    main()
