#!/usr/bin/env python3
"""Finite checks for the binary Cayley double-cover obstruction; stdlib only.

The companion note contains the uniform proof. No A-REG theorem is claimed.
"""

from itertools import combinations


def lift(n, edges, signs):
    adjacency = [set() for _ in range(2 * n)]
    for j, (u, v) in enumerate(edges):
        bit = (signs >> j) & 1
        for sheet in (0, 1):
            a, b = 2 * u + sheet, 2 * v + (sheet ^ bit)
            adjacency[a].add(b)
            adjacency[b].add(a)
    assert all(v not in neighbors for v, neighbors in enumerate(adjacency))
    assert all(v in adjacency[w] for v, ns in enumerate(adjacency) for w in ns)
    return adjacency


def c4_free(adjacency):
    return all(len(adjacency[u] & adjacency[v]) <= 1
               for u, v in combinations(range(len(adjacency)), 2))


def set_conditions(connection):
    pair_sums = [s ^ t for s, t in combinations(connection, 2)]
    return (len(set(pair_sums)) == len(pair_sums),
            not (set(pair_sums) & set(connection)))


def main():
    for label, n, edges in [
        ("K4", 4, list(combinations(range(4), 2))),
        ("K2,3", 5, [(u, v) for u in range(2) for v in range(2, 5)]),
    ]:
        for signs in range(1 << len(edges)):
            assert not c4_free(lift(n, edges, signs)), (label, signs)
        print(f"{label}: all {1 << len(edges)} double covers contain C4 PASS")

    # Independent small-group census: no signing enumeration is needed here.
    rejected = {"repeated_pair_sum": 0, "zero_sum_triple": 0}
    for connection in combinations(range(1, 8), 4):
        sidon, sum_free = set_conditions(connection)
        assert not (sidon and sum_free), connection
        key = "repeated_pair_sum" if not sidon else "zero_sum_triple"
        rejected[key] += 1
        if sidon:
            s, t = next((s, t) for s, t in combinations(connection, 2)
                        if s ^ t in connection)
            clique = {0, s, t, s ^ t}
            assert len(clique) == 4
            assert all(u ^ v in connection for u, v in combinations(clique, 2))
    assert sum(rejected.values()) == 35
    print(f"F2^3, degree 4: all 35 connection sets excluded {rejected} PASS")

    for r in range(1, 5):
        accepted = 0
        vertices = range(1, 1 << r)
        for d in range(1 << r):
            for connection in combinations(vertices, d):
                if all(set_conditions(connection)):
                    assert 1 + d + d * (d - 1) // 2 <= 1 << r
                    accepted += 1
        print(f"F2^{r}: all {1 << ((1 << r) - 1)} subsets checked; "
              f"{accepted} sum-free Sidon sets obey bound PASS")

    # An odd voltage around C4 produces a genuine C4-free cover, C8.
    cycle_edges = [(0, 1), (1, 2), (2, 3), (0, 3)]
    adjacency = lift(4, cycle_edges, 1)
    assert c4_free(adjacency)
    assert {len(ns) for ns in adjacency} == {2}
    reached, pending = {0}, [0]
    while pending:
        v = pending.pop()
        for w in adjacency[v] - reached:
            reached.add(w)
            pending.append(w)
    assert len(reached) == 8 == 2**2 + 2 + 2
    print("Positive control C8: connected, degree 2, C4-free, bound sharp PASS")


if __name__ == "__main__":
    main()
