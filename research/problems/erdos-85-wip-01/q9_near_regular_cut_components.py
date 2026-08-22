#!/usr/bin/env python3
"""Verify the near-regular cut component arithmetic for B.3.

This is an exact integer checker for the necessary component conditions in
``B3_NEAR_REGULAR_CUT_VARIANCE_AUDIT.md``.  It is not a graph census and does
not assert that any surviving row is realizable.
"""

from itertools import product


N_ORDINARY = 78
Q = 9
HIGH_DEGREE = 10
TARGET_BETA = (10, 10, 10)


def balanced_square_sum(total: int, count: int = N_ORDINARY) -> int:
    base, remainder = divmod(total, count)
    return (count - remainder) * base * base + remainder * (base + 1) ** 2


def cut_lower(order: int, beta: tuple[int, int, int]) -> int:
    ordinary_degree_sum = Q * order - sum(beta)
    return (
        balanced_square_sum(ordinary_degree_sum)
        - order * order
        + sum(value * (value - 1) for value in beta)
    )


def admissible_types() -> dict[int, list[tuple[int, int, int]]]:
    result = {}
    for order in range(1, N_ORDINARY):
        types = []
        for beta in product(range(HIGH_DEGREE + 1), repeat=3):
            complement = tuple(HIGH_DEGREE - value for value in beta)
            if sum(beta) % 2:
                continue
            if cut_lower(order, beta) <= 0 and cut_lower(
                N_ORDINARY - order, complement
            ) <= 0:
                types.append(beta)
        if types:
            result[order] = types
    return result


def order_partitions(orders: list[int]) -> list[tuple[int, ...]]:
    result = []

    def visit(remaining: int, first: int, parts: list[int]) -> None:
        if remaining == 0:
            if len(parts) >= 2:
                result.append(tuple(parts))
            return
        for index in range(first, len(orders)):
            order = orders[index]
            if order > remaining:
                break
            visit(remaining - order, index, parts + [order])

    visit(N_ORDINARY, 0, [])
    return result


def color_assignment_count(
    partition: tuple[int, ...], types: dict[int, list[tuple[int, int, int]]]
) -> int:
    return sum(
        tuple(map(sum, zip(*assignment))) == TARGET_BETA
        for assignment in product(*(types[order] for order in partition))
    )


def tripartite_two_factor_necessary(color_counts: tuple[int, int, int]) -> bool:
    """Necessary conditions for a simple 2-factor with independent colors."""
    a, b, c = color_counts
    if min(color_counts) < 0:
        return False
    if a + b + c == 0:
        return True
    if a + b + c < 3:
        return False
    edge_counts = (a + b - c, a + c - b, b + c - a)
    capacities = (a * b, a * c, b * c)
    return all(0 <= edges <= capacity for edges, capacity in zip(edge_counts, capacities))


def bin_degree_ledger_necessary(
    order: int, beta: tuple[int, int, int], owns_b3: bool
) -> bool:
    """Necessary B0/B1/B3 edge capacities inside one D0-component."""
    owner = int(owns_b3)
    bin_one = sum(beta) - 3 * owner
    bin_zero = order - bin_one - owner
    if bin_zero < 0 or bin_one < 0:
        return False
    # Every B1 vertex has five B0 defect neighbors; B3 has five as well.
    if bin_one > 0 and bin_zero < 5:
        return False
    if owner and bin_zero < 5:
        return False
    # The B0 degree sum determines twice the number of internal B0 edges.
    twice_bin_zero_edges = 8 * bin_zero - 5 * bin_one - 5 * owner
    return (
        twice_bin_zero_edges % 2 == 0
        and 0 <= twice_bin_zero_edges <= bin_zero * (bin_zero - 1)
    )


def localized_assignment_counts(
    partition: tuple[int, ...], types: dict[int, list[tuple[int, int, int]]]
) -> tuple[int, int, set[int]]:
    """Count assignments/placements surviving B1-cycle localization.

    The distinguished component index is the component containing the unique
    B3 vertex.  Its B1 color counts are beta - (1,1,1); every other
    component's B1 color counts are beta.
    """
    assignments = set()
    placements = []
    owner_orders = set()
    for assignment in product(*(types[order] for order in partition)):
        if tuple(map(sum, zip(*assignment))) != TARGET_BETA:
            continue
        for owner in range(len(partition)):
            color_counts = [
                tuple(value - (index == owner) for value in beta)
                for index, beta in enumerate(assignment)
            ]
            if all(tripartite_two_factor_necessary(counts) for counts in color_counts):
                assignments.add(assignment)
                placements.append((assignment, owner))
                owner_orders.add(partition[owner])
    return len(assignments), len(placements), owner_orders


def bin_ledger_assignment_counts(
    partition: tuple[int, ...], types: dict[int, list[tuple[int, int, int]]]
) -> tuple[int, int, set[int]]:
    """Further refine localized placements by the exact bin-degree ledger."""
    assignments = set()
    placements = []
    owner_orders = set()
    for assignment in product(*(types[order] for order in partition)):
        if tuple(map(sum, zip(*assignment))) != TARGET_BETA:
            continue
        for owner in range(len(partition)):
            color_counts = [
                tuple(value - (index == owner) for value in beta)
                for index, beta in enumerate(assignment)
            ]
            if not all(tripartite_two_factor_necessary(counts) for counts in color_counts):
                continue
            if not all(
                bin_degree_ledger_necessary(order, beta, index == owner)
                for index, (order, beta) in enumerate(zip(partition, assignment))
            ):
                continue
            assignments.add(assignment)
            placements.append((assignment, owner))
            owner_orders.add(partition[owner])
    return len(assignments), len(placements), owner_orders


def order_nine_owner_types(
    partitions: list[tuple[int, ...]], types: dict[int, list[tuple[int, int, int]]]
) -> set[tuple[int, int, int]]:
    """Profiles possible when the B3 vertex lies in an order-nine component."""
    result = set()
    for partition in partitions:
        for assignment in product(*(types[order] for order in partition)):
            if tuple(map(sum, zip(*assignment))) != TARGET_BETA:
                continue
            for owner, order in enumerate(partition):
                color_counts = [
                    tuple(value - (index == owner) for value in beta)
                    for index, beta in enumerate(assignment)
                ]
                if order == 9 and all(
                    tripartite_two_factor_necessary(counts) for counts in color_counts
                ):
                    result.add(assignment[owner])
    return result


def main() -> None:
    types = admissible_types()
    orders = sorted(types)
    partitions = order_partitions(orders)

    expected_orders = [9, 18, 19, 26, 27, 35, 43, 51, 52, 59, 60, 69]
    expected_partitions = [
        (9, 9, 9, 51),
        (9, 9, 60),
        (9, 18, 51),
        (9, 26, 43),
        (9, 69),
        (18, 60),
        (19, 59),
        (26, 26, 26),
        (26, 52),
        (27, 51),
        (35, 43),
    ]
    assert orders == expected_orders
    assert partitions == expected_partitions

    counts = [color_assignment_count(parts, types) for parts in partitions]
    assert counts == [39, 39, 10, 9, 10, 10, 6, 6, 3, 1, 3]

    localized = [localized_assignment_counts(parts, types) for parts in partitions]
    assert [entry[0] for entry in localized] == [21, 27, 7, 9, 7, 10, 6, 6, 3, 1, 3]
    assert [entry[1] for entry in localized] == [21, 33, 12, 18, 8, 17, 12, 18, 6, 2, 6]
    assert [entry[2] for entry in localized] == [
        {51},
        {9, 60},
        {9, 18, 51},
        {26, 43},
        {9, 69},
        {18, 60},
        {19, 59},
        {26},
        {26, 52},
        {27, 51},
        {35, 43},
    ]
    assert order_nine_owner_types(partitions, types) == {(2, 2, 2)}

    bin_ledger = [bin_ledger_assignment_counts(parts, types) for parts in partitions]
    assert [entry[0] for entry in bin_ledger] == [21, 27, 7, 9, 7, 10, 6, 6, 3, 1, 3]
    assert [entry[1] for entry in bin_ledger] == [21, 27, 10, 18, 7, 17, 12, 18, 6, 2, 6]

    print(f"verified component orders: {orders}")
    for parts, count, (assignment_count, placement_count, owner_orders), ledger in zip(
        partitions, counts, localized, bin_ledger
    ):
        print(
            f"{parts}: color assignments={count}, localized={assignment_count}, "
            f"B3 placements={placement_count}, B3 component orders={sorted(owner_orders)}, "
            f"bin-ledger placements={ledger[1]}"
        )


if __name__ == "__main__":
    main()
