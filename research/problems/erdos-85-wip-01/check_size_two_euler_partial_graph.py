#!/usr/bin/env python3
"""Verify a C4-free partial carrier extension, not a regular ambient witness."""

from itertools import combinations


# Cyclic vertex sequence of an Euler tour in K_16 minus C_16 and antipodes.
TOUR = [
    0, 6, 15, 10, 7, 1, 6, 12, 15, 8, 4, 14, 0, 11, 1, 14,
    12, 0, 13, 4, 7, 3, 13, 6, 2, 4, 11, 8, 3, 10, 14, 7,
    5, 3, 14, 11, 13, 2, 0, 10, 1, 8, 12, 5, 1, 15, 11, 2,
    9, 12, 10, 8, 2, 14, 9, 15, 4, 10, 13, 9, 5, 10, 6, 8,
    5, 11, 7, 12, 3, 6, 9, 0, 3, 1, 13, 8, 14, 5, 2, 15,
    13, 7, 2, 12, 1, 4, 6, 11, 9, 7, 0, 4, 9, 3, 15, 5,
]


def check():
    q, n, size = 16, 14, 32
    h_steps = {1, size - 1}
    d_steps = (set(range(1, size, 2)) - h_steps) | {q}
    l_steps = set(range(1, size)) - d_steps - {2, size - 2}
    selectors = [(a, b) for a in range(size) for b in range(a + 1, size)
                 if (b - a) % size in l_steps]
    label = {edge: size + i for i, edge in enumerate(selectors)}
    assert size + len(selectors) == q * q
    graph = [set() for _ in range(q * q)]

    def add(a, b):
        assert a != b
        graph[a].add(b)
        graph[b].add(a)

    for a in range(size):
        add(a, (a + 1) % size)
    for edge, f in label.items():
        for a in edge:
            add(a, f)

    tour_edges = [tuple(sorted((TOUR[i], TOUR[(i + 1) % len(TOUR)])))
                  for i in range(len(TOUR))]
    expected = {(a, b) for a in range(q) for b in range(a + 1, q)
                if (b - a) % q not in {1, q - 1, q // 2}}
    assert len(tour_edges) == len(set(tour_edges)) == q * (q - 4) // 2
    assert set(tour_edges) == expected
    # Every cyclic segment of at most three edges is a path.
    assert all(len({TOUR[(i + j) % len(TOUR)] for j in range(length + 1)})
               == length + 1 for i in range(len(TOUR)) for length in (1, 2, 3))
    for parity in (0, 1):
        cycle = [label[tuple(2 * a + parity for a in edge)] for edge in tour_edges]
        for i, f in enumerate(cycle):
            add(f, cycle[(i + 1) % len(cycle)])

    # Check the entire graph, including C/F mixed pairs, not only J cycles.
    assert all(len(graph[a] & graph[b]) <= 1
               for a, b in combinations(range(q * q), 2))
    assert all(len(graph[a]) == q for a in range(size))
    for edge, f in label.items():
        assert len(graph[f]) == (4 if sum(edge) % 2 == 0 else 2)
        incident_neighbors = [g for other, g in label.items()
                              if g in graph[f] and set(edge) & set(other)]
        assert len(incident_neighbors) == (2 if sum(edge) % 2 == 0 else 0)
    # The C-shore Gram remains exactly the prescribed one.
    for a in range(size):
        for b in range(size):
            assert len(graph[a] & graph[b]) == ((q - 1) * (a == b) + 1
                                               - ((b - a) % size in d_steps))
    degrees = {degree: sum(len(neighbors) == degree for neighbors in graph)
               for degree in sorted({len(s) for s in graph})}
    assert degrees == {2: 32, 4: 192, 16: 32}
    print(dict(q=q, vertices=q * q, euler_tour_length=len(TOUR),
               c4_free=True, degree_histogram=degrees,
               regular_ambient_witness=False))


if __name__ == "__main__":
    check()
