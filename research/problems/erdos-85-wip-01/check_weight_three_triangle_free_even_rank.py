#!/usr/bin/env python3
"""Exact triangle-free counterexample to forced odd closed-neighborhood rank.

No solver or third-party dependency. This constructs only a defect graph;
there is no ambient H, B, or regular C4-free completion.
"""

from itertools import combinations


SWITCHES = [
    (19, 46, 34, 14),
    (35, 17, 2, 32),
    (4, 26, 20, 41),
    (38, 20, 22, 5),
    (28, 7, 12, 39),
    (39, 13, 12, 28),
    (22, 43, 5, 27),
    (5, 23, 27, 8),
    (38, 15, 20, 0),
]


def binary_rank(rows):
    """Gaussian elimination over F2, using exact bit rows."""
    basis = {}
    for row in rows:
        while row:
            pivot = row.bit_length() - 1
            if pivot in basis:
                row ^= basis[pivot]
            else:
                basis[pivot] = row
                break
    return len(basis)


def closed_rows(graph):
    return [(1 << x) | sum(1 << y for y in row)
            for x, row in enumerate(graph)]


def verify_graph(graph):
    assert len(graph) == 48
    for x, row in enumerate(graph):
        assert len(row) == 15 and x not in row
        for y in row:
            assert x in graph[y]
            assert not (row & graph[y]), "triangle"
    reached, todo = {0}, [0]
    while todo:
        for y in graph[todo.pop()] - reached:
            reached.add(y)
            todo.append(y)
    assert len(reached) == 48


def construct():
    graph = [{y for y in range(48) if 16 < (y-x) % 48 < 32}
             for x in range(48)]
    verify_graph(graph)
    assert binary_rank(closed_rows(graph)) == 33
    for a, b, c, d in SWITCHES:
        assert len({a, b, c, d}) == 4
        assert b in graph[a] and d in graph[c]
        assert c not in graph[a] and d not in graph[b]
        for x, y in ((a, b), (c, d)):
            graph[x].remove(y)
            graph[y].remove(x)
        assert not (graph[a] & graph[c])
        assert not (graph[b] & graph[d])
        for x, y in ((a, c), (b, d)):
            graph[x].add(y)
            graph[y].add(x)
        verify_graph(graph)
    return graph


def main():
    graph = construct()
    cycle = [0, 17, 34, 3, 22]
    for i, j in combinations(range(5), 2):
        assert (cycle[j] in graph[cycle[i]]) == (j-i in (1, 4))
    rank = binary_rank(closed_rows(graph))
    assert rank == 46
    # In an exact perfect code, disjoint closed neighborhoods of size16
    # partition48 vertices, so the code must have size3. Check every such
    # triple directly, independently of the rank-parity theorem.
    codes = 0
    for code in combinations(range(48), 3):
        selected = set(code)
        codes += all(len((graph[x] | {x}) & selected) == 1 for x in range(48))
    assert codes == 0
    print("PASS: connected triangle-free nonbipartite 15-regular D on48 vertices")
    print(f"Nine valid switches; rank_F2(D+I)={rank}; induced C5={cycle}; perfect codes={codes}")
    print("No H, B, or ambient completion is supplied")


if __name__ == "__main__":
    main()
