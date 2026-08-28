#!/usr/bin/env python3
"""Verify the coherent K4,4 shore-trade normal form of sixteenRegular."""

from itertools import combinations, permutations


EDGES = [
    (0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 8), (1, 13),
    (2, 6), (2, 12), (3, 7), (3, 11), (3, 15), (4, 5), (4, 10),
    (4, 14), (5, 6), (5, 10), (5, 15), (6, 12), (6, 15), (7, 9),
    (7, 10), (7, 11), (8, 9), (8, 13), (8, 15), (9, 10), (9, 12),
    (11, 13), (11, 14), (12, 14), (13, 14),
]


def build_adjacency() -> list[list[int]]:
    adjacency = [[0] * 16 for _ in range(16)]
    for x, y in EDGES:
        adjacency[x][y] = adjacency[y][x] = 1
    return adjacency


def defect_components(adjacency: list[list[int]]) -> list[list[int]]:
    defect = [[0] * 16 for _ in range(16)]
    for x in range(16):
        for y in range(x + 1, 16):
            common = sum(adjacency[z][x] * adjacency[z][y] for z in range(16))
            if common == 0:
                defect[x][y] = defect[y][x] = 1

    components = []
    unseen = set(range(16))
    while unseen:
        root = min(unseen)
        unseen.remove(root)
        stack = [root]
        component = []
        while stack:
            x = stack.pop()
            component.append(x)
            neighbors = {y for y in unseen if defect[x][y]}
            unseen -= neighbors
            stack.extend(neighbors)
        components.append(sorted(component))
    return components


def row_edges(adjacency: list[list[int]], component: list[int]) -> list[tuple[int, int]]:
    result = []
    for row in range(16):
        endpoints = tuple(i for i, x in enumerate(component) if adjacency[row][x])
        assert len(endpoints) == 2
        result.append(endpoints)
    assert len(set(result)) == 16
    return result


def best_split_trades(edges: list[tuple[int, int]]):
    edge_set = set(edges)
    vertices = set(range(8))
    trades = []
    for shore_tuple in combinations(range(8), 4):
        shore = set(shore_tuple)
        cross = {
            tuple(sorted((x, y)))
            for x in shore
            for y in vertices - shore
        }
        if len(edge_set & cross) == 12:
            trades.append((shore, cross - edge_set, edge_set - cross))
    assert len(trades) == 4
    return trades


def is_rectangle_partition(first, second) -> bool:
    cells = set()
    for edge0, edge1 in zip(first, second):
        for x in edge0:
            for y in edge1:
                if (x, y) in cells:
                    return False
                cells.add((x, y))
    return len(cells) == 64


def main() -> None:
    adjacency = build_adjacency()
    components = defect_components(adjacency)
    assert components == [
        [0, 3, 4, 8, 9, 12, 14, 15],
        [1, 2, 5, 6, 7, 10, 11, 13],
    ]
    actual = [row_edges(adjacency, component) for component in components]
    trades = [best_split_trades(edges) for edges in actual]

    solutions = []
    for cut0, (shore0, removed0, added0) in enumerate(trades[0]):
        changed_rows0 = [row for row, edge in enumerate(actual[0]) if edge in added0]
        for cut1, (shore1, removed1, added1) in enumerate(trades[1]):
            changed_rows1 = [row for row, edge in enumerate(actual[1]) if edge in added1]
            for assignment0 in permutations(sorted(removed0)):
                repaired0 = list(actual[0])
                for row, edge in zip(changed_rows0, assignment0):
                    repaired0[row] = edge
                for assignment1 in permutations(sorted(removed1)):
                    repaired1 = list(actual[1])
                    for row, edge in zip(changed_rows1, assignment1):
                        repaired1[row] = edge
                    if is_rectangle_partition(repaired0, repaired1):
                        solutions.append((cut0, cut1, shore0, shore1))

    # There is exactly one coherent repair for every ordered pair of the four
    # maximizing shore cuts.
    assert len(solutions) == 16
    assert {(cut0, cut1) for cut0, cut1, _, _ in solutions} == {
        (cut0, cut1) for cut0 in range(4) for cut1 in range(4)
    }
    print("q4 coherent affine shore-trade verification: PASS (16 repairs)")


if __name__ == "__main__":
    main()
