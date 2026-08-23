#!/usr/bin/env python3
"""Exhaust the four outward A_e bits on the known one-edge local skeleton."""

from itertools import combinations, product


VERTICES = ("x-", "x+", "a-", "a+", "p", "p-", "p+", "q-", "q+")
BASE_EDGES = {
    frozenset(edge)
    for edge in (
        ("x-", "x+"),
        ("x-", "p"),
        ("x-", "p-"),
        ("x+", "p"),
        ("x+", "p+"),
        ("a-", "p-"),
        ("a-", "q-"),
        ("a+", "p+"),
        ("a+", "q+"),
    )
}
INTERFACE_EDGES = (
    ("q-", "p-"),
    ("q-", "p+"),
    ("q+", "p-"),
    ("q+", "p+"),
)


def c4_witness(edges: set[frozenset[str]]) -> tuple[str, str, list[str]] | None:
    for left, right in combinations(VERTICES, 2):
        common = [
            vertex
            for vertex in VERTICES
            if frozenset((left, vertex)) in edges
            and frozenset((right, vertex)) in edges
        ]
        if len(common) >= 2:
            return left, right, common
    return None


def main() -> None:
    admissible = []
    for bits in product((0, 1), repeat=4):
        edges = BASE_EDGES | {
            frozenset(INTERFACE_EDGES[index])
            for index, bit in enumerate(bits)
            if bit
        }
        witness = c4_witness(edges)
        if witness is None:
            admissible.append(bits)
        else:
            print(f"excluded={''.join(map(str, bits))} witness={witness}")

    odd = [bits for bits in admissible if sum(bits) % 2 == 1]
    print(f"admissible={len(admissible)} odd_admissible={len(odd)}")
    assert len(admissible) == 15
    assert len(odd) == 8
    assert (1, 1, 1, 1) not in admissible

    # Abstract two-factor completion showing that cycle-cover structure and
    # closed-B-neighborhood A-independence still permit an odd interface.
    b_order = tuple(range(9))
    a_order = (8, 7, 0, 2, 4, 1, 3, 5, 6)

    def cycle_edges(order: tuple[int, ...]) -> set[frozenset[int]]:
        return {
            frozenset((order[index], order[(index + 1) % len(order)]))
            for index in range(len(order))
        }

    b_edges = cycle_edges(b_order)
    a_edges = cycle_edges(a_order)
    private = {8, 1}
    outward = {7, 2}
    closed_b_neighborhood = {8, 0, 1}
    interface = sum(
        bool(edge & private) and bool(edge & outward) for edge in a_edges
    )
    induced = sum(edge <= closed_b_neighborhood for edge in a_edges)
    assert len(b_edges) == len(a_edges) == 9
    assert induced == 0
    assert interface == 1
    print(
        "two_factor_completion=odd "
        f"interface={interface} induced_closed_B={induced}"
    )


if __name__ == "__main__":
    main()
