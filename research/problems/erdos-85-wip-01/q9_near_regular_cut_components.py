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

    print(f"verified component orders: {orders}")
    for parts, count in zip(partitions, counts):
        print(f"{parts}: color assignments={count}")


if __name__ == "__main__":
    main()
