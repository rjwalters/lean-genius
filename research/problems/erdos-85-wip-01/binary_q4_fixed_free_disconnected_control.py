#!/usr/bin/env python3
"""Exact q=4 control for the proposed Baer-type A-REG theorem.

The hard-coded graph is loopless, symmetric, 4-regular and C4-free on
4^2 vertices.  Its second-order defect graph has two components of order
eight, so it does not contradict NONBIP-CONNECTED.  It does show that q=4
is a genuine exception to any theorem without the standing k >= 3
hypothesis.  Its triangle-free-edge graph is one C8 contained in only one
defect component, refuting componentwise T-detection and cycle-local
holonomy arguments.

This script uses only the Python standard library and checks every claim
directly from the edge list.
"""

from collections import deque
from collections import Counter


Q = 4
N = Q * Q
A_EDGES = {
    (0, 1), (0, 2), (0, 5), (0, 9),
    (1, 4), (1, 5), (1, 10),
    (2, 3), (2, 7), (2, 9),
    (3, 7), (3, 10), (3, 11),
    (4, 6), (4, 10), (4, 12),
    (5, 8), (5, 11),
    (6, 8), (6, 9), (6, 12),
    (7, 8), (7, 15),
    (8, 15),
    (9, 13),
    (10, 13),
    (11, 12), (11, 14),
    (12, 14),
    (13, 14), (13, 15),
    (14, 15),
}


def adjacency(edges: set[tuple[int, int]]) -> list[set[int]]:
    neighbors = [set() for _ in range(N)]
    for x, y in edges:
        assert 0 <= x < y < N
        neighbors[x].add(y)
        neighbors[y].add(x)
    return neighbors


def components(neighbors: list[set[int]]) -> list[frozenset[int]]:
    unseen = set(range(N))
    answer = []
    while unseen:
        root = min(unseen)
        reached = {root}
        queue = deque([root])
        while queue:
            x = queue.popleft()
            for y in neighbors[x] - reached:
                reached.add(y)
                queue.append(y)
        unseen -= reached
        answer.append(frozenset(reached))
    return sorted(answer, key=lambda part: min(part))


def main() -> None:
    a = adjacency(A_EDGES)
    assert all(x not in a[x] for x in range(N))
    assert all(len(a[x]) == Q for x in range(N))

    # A simple graph is C4-free exactly when every pair has at most one
    # common neighbor.
    common = {
        (x, y): len(a[x] & a[y])
        for x in range(N)
        for y in range(x + 1, N)
    }
    assert max(common.values()) == 1

    d_edges = {pair for pair, count in common.items() if count == 0}
    d = adjacency(d_edges)
    assert all(len(d[x]) == Q - 1 for x in range(N))
    d_components = components(d)
    assert d_components == [
        frozenset({0, 1, 2, 4, 7, 12, 14, 15}),
        frozenset({3, 5, 6, 8, 9, 10, 11, 13}),
    ]

    # Candidate-(vi) incidence-bottleneck calibration.  Entrywise,
    # E = AD - (J-A).  Every row has energy six, so this exact ambient
    # binary-incidence control violates the proposed cubic upper bound
    # ||E||_F^2 <= q^3: its total is 96 rather than 64.  Since D is
    # disconnected and q=4, a viable upper theorem must genuinely use both
    # connectedness and the standing k>=3 hypothesis.
    incidence_error = [
        [
            sum(1 for z in a[x] if y in d[z]) - (1 - int(y in a[x]))
            for y in range(N)
        ]
        for x in range(N)
    ]
    row_energies = [sum(value * value for value in row) for row in incidence_error]
    total_energy = sum(row_energies)
    assert row_energies == [6] * N
    assert total_energy == 96 > Q ** 3 == 64

    t_edges = A_EDGES & d_edges
    t = adjacency(t_edges)
    assert t_edges == {
        (3, 10), (3, 11), (5, 8), (5, 11),
        (6, 8), (6, 9), (9, 13), (10, 13),
    }
    assert sorted(len(t[x]) for x in range(N)) == [0] * 8 + [2] * 8
    nontrivial_t_components = [part for part in components(t) if len(part) > 1]
    assert nontrivial_t_components == [d_components[1]]

    # Baer-overlap transport calibration.  Modulo two the overlap graph has
    # adjacency M_Omega = A^3 + J + I, so off the diagonal a pair belongs to
    # Omega exactly when its number of A-three-walks is even.
    def three_walks(x: int, y: int) -> int:
        return sum(1 for u in a[x] for v in a[y] if v in a[u])

    omega_edges = {
        (x, y)
        for x in range(N)
        for y in range(x + 1, N)
        if (three_walks(x, y) + 1) % 2 == 1
    }
    h_edges = omega_edges ^ d_edges
    k_edges = h_edges ^ t_edges
    h = adjacency(h_edges)
    k = adjacency(k_edges)

    assert h_edges & A_EDGES == t_edges
    assert not (k_edges & A_EDGES)
    assert all(len(h[x]) % 2 == 0 for x in range(N))
    assert all(len(k[x]) % 2 == 0 for x in range(N))
    assert (len(d_edges), len(t_edges), len(omega_edges), len(h_edges), len(k_edges)) == (
        24, 8, 40, 48, 40
    )
    assert sorted(len(k[x]) for x in range(N)) == [4] * 8 + [6] * 8
    assert len(k_edges & d_edges) == 8
    assert len(k_edges - d_edges) == 32

    # Goal-#36 semipartial-geometry calibration.  One proposed completion
    # route asks for a two-valued 0/t law for A^3 on nonincident point-line
    # pairs.  The exact fixed-free q=4 control has three positive values
    # there, so that law is not a generic consequence of self-polar regular
    # C4-free incidence.  Any promotion to semipartial uniformity must use
    # both connectedness and the standing k>=3 hypothesis essentially.
    nonedges = {
        (x, y)
        for x in range(N)
        for y in range(x + 1, N)
        if y not in a[x]
    }
    nonedge_cubic_distribution = Counter(three_walks(x, y) for x, y in nonedges)
    assert nonedge_cubic_distribution == Counter({3: 48, 2: 20, 4: 20})
    assert len(nonedge_cubic_distribution) == 3

    # The other proposed semipartial uniformity, constancy of D^2 on
    # D-edges, happens to hold in this control (with value zero).  Hence the
    # cubic 0/t law is the first condition genuinely separated by the model;
    # the D^2 condition alone cannot be terminal.
    defect_edge_codegrees = Counter(len(d[x] & d[y]) for x, y in d_edges)
    assert defect_edge_codegrees == Counter({0: 24})

    # The two nonconstant F_2 adjacency-kernel shores are exactly the two D
    # components.  On each, K- and T-incidence agree vertexwise modulo two.
    kernel_shores = {
        frozenset(x for x in range(N) if (mask >> x) & 1)
        for mask in range(1 << N)
        if all(
            sum((mask >> y) & 1 for y in a[x]) % 2 == 0
            for x in range(N)
        )
    }
    assert kernel_shores == {
        frozenset(), frozenset(range(N)), *d_components
    }
    for shore in d_components:
        assert all(len(a[x] & shore) % 2 == 0 for x in range(N))
        half_occupancy = [len(a[x] & shore) // 2 for x in range(N)]
        assert half_occupancy == [1] * N
        assert all(
            len(k[x] & shore) % 2 == len(t[x] & shore) % 2
            for x in range(N)
        )
        assert sum(1 for x, y in k_edges if (x in shore) != (y in shore)) == 32

    print("verified: symmetric loopless 4-regular C4-free A on 16 vertices")
    print("trace(A) = 0; D components = [8, 8]; T is one C8")
    print("incidence bottleneck: row energies 6^16, total 96 > q^3=64")
    print("Baer transport: |Omega|=40, |H|=48, |K|=40; K degrees 4^8 6^8")
    print("semipartial calibration: A^3 nonedge values 2^20 3^48 4^20; D^2=0 on D")


if __name__ == "__main__":
    main()
