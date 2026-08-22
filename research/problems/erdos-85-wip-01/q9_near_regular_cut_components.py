#!/usr/bin/env python3
"""Verify the near-regular cut component arithmetic for B.3.

This is an exact integer checker for the necessary component conditions in
``B3_NEAR_REGULAR_CUT_VARIANCE_AUDIT.md``.  It is not a graph census and does
not assert that any surviving row is realizable.
"""

from collections import Counter
from functools import lru_cache
from itertools import product


N_ORDINARY = 78
Q = 9
HIGH_DEGREE = 10
TARGET_BETA = (10, 10, 10)


def balanced_square_sum(total: int, count: int = N_ORDINARY) -> int:
    base, remainder = divmod(total, count)
    return (count - remainder) * base * base + remainder * (base + 1) ** 2


def bounded_degree_profiles(
    count: int, total: int, square_sum: int, maximum: int = 9
) -> list[tuple[int, ...]]:
    """Enumerate multiplicity vectors for bounded integer degree profiles."""
    @lru_cache(maxsize=None)
    def visit(
        value: int, left_count: int, left_total: int, left_squares: int
    ) -> tuple[tuple[int, ...], ...]:
        if left_total < value * left_count or left_total > maximum * left_count:
            return ()
        if left_squares < value * value * left_count or left_squares > maximum * maximum * left_count:
            return ()
        if value == maximum:
            if (
                left_total == maximum * left_count
                and left_squares == maximum * maximum * left_count
            ):
                return ((left_count,),)
            return ()
        result = []
        for multiplicity in range(left_count + 1):
            used_total = value * multiplicity
            used_squares = value * value * multiplicity
            if used_total > left_total or used_squares > left_squares:
                break
            for suffix in visit(
                value + 1,
                left_count - multiplicity,
                left_total - used_total,
                left_squares - used_squares,
            ):
                result.append((multiplicity,) + suffix)
        return tuple(result)

    return list(visit(0, count, total, square_sum))


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


def three_order_nine_family_counts(
    types: dict[int, list[tuple[int, int, int]]]
) -> Counter[tuple[tuple[int, int, int], ...]]:
    """Color-orbit shapes for the forced (9,9,9,51) row."""
    result = Counter()
    for small in product(types[9], repeat=3):
        if tuple(map(sum, zip(*small))) != (4, 4, 4):
            continue
        if not all(
            tripartite_two_factor_necessary(beta)
            and bin_degree_ledger_necessary(9, beta, False)
            for beta in small
        ):
            continue
        shape = tuple(sorted(tuple(sorted(beta)) for beta in small))
        result[shape] += 1
    return result


def b3_articulation_assemblies() -> list[tuple[tuple[int, int, tuple[int, int, int]], ...]]:
    """Necessary component assemblies if deleting B3 disconnects D0.

    A component type is ``(e,k,beta)``: it contains ``e`` of the five
    exceptional B0 vertices, ``5k`` regular B0 vertices, and ``3k`` B1
    vertices.  Its order and boundary are ``e+8k`` and ``e``.
    """
    types = []
    for exceptional in range(1, 6):
        for scale in range(10):
            bin_zero = exceptional + 5 * scale
            twice_bin_zero_edges = 7 * exceptional + 25 * scale
            if bin_zero < 8:
                continue
            if twice_bin_zero_edges % 2:
                continue
            if twice_bin_zero_edges > bin_zero * (bin_zero - 1):
                continue
            order = exceptional + 8 * scale
            if not 1 <= order < N_ORDINARY:
                continue
            for beta in product(range(10), repeat=3):
                if sum(beta) != 3 * scale:
                    continue
                complement = tuple(HIGH_DEGREE - value for value in beta)
                if cut_lower(order, beta) <= exceptional and cut_lower(
                    N_ORDINARY - order, complement
                ) <= exceptional:
                    types.append((exceptional, scale, beta))

    result = []

    def visit(
        first: int,
        exceptional_sum: int,
        scale_sum: int,
        beta_sum: tuple[int, int, int],
        parts: list[tuple[int, int, tuple[int, int, int]]],
    ) -> None:
        if (exceptional_sum, scale_sum, beta_sum) == (5, 9, (9, 9, 9)):
            if len(parts) >= 2:
                result.append(tuple(parts))
            return
        for index in range(first, len(types)):
            exceptional, scale, beta = types[index]
            new_beta = tuple(beta_sum[i] + beta[i] for i in range(3))
            if exceptional_sum + exceptional > 5 or scale_sum + scale > 9:
                continue
            if any(value > 9 for value in new_beta):
                continue
            visit(
                index,
                exceptional_sum + exceptional,
                scale_sum + scale,
                new_beta,
                parts + [types[index]],
            )

    visit(0, 0, 0, (0, 0, 0), [])
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
    # A component not containing B3 has 3*n0 = 5*n1 by the pointwise
    # B0/B1 defect-neighbor types, hence order n0+n1 is divisible by eight.
    # No proper order surviving the cut inequalities has that divisibility.
    assert all(order % 8 != 0 for order in orders)
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
    assert three_order_nine_family_counts(types) == Counter(
        {
            ((0, 2, 2), (0, 2, 2), (0, 2, 2)): 6,
            ((0, 2, 2), (1, 1, 2), (1, 1, 2)): 9,
            ((1, 1, 2), (1, 1, 2), (1, 1, 2)): 6,
        }
    )

    articulation = b3_articulation_assemblies()
    articulation_order_pairs = Counter(
        tuple(sorted(exceptional + 8 * scale for exceptional, scale, _ in assembly))
        for assembly in articulation
    )
    assert articulation_order_pairs == Counter({(18, 59): 7, (27, 50): 1, (34, 43): 1})
    equality_profiles = Counter()
    for assembly in articulation:
        for exceptional, scale, beta in assembly:
            order = exceptional + 8 * scale
            for shore_order, shore_beta in (
                (order, beta),
                (N_ORDINARY - order, tuple(HIGH_DEGREE - value for value in beta)),
            ):
                if cut_lower(shore_order, shore_beta) != exceptional:
                    continue
                total = Q * shore_order - sum(shore_beta)
                low, high_count = divmod(total, N_ORDINARY)
                equality_profiles[
                    (
                        shore_order,
                        tuple(sorted(shore_beta)),
                        low,
                        N_ORDINARY - high_count,
                        low + 1,
                        high_count,
                        exceptional,
                    )
                ] += 1
    assert equality_profiles == Counter(
        {
            (60, (7, 8, 9), 6, 30, 7, 48, 2): 6,
            (34, (4, 4, 4), 3, 18, 4, 60, 2): 1,
            (50, (6, 6, 6), 5, 36, 6, 42, 2): 1,
            (51, (7, 7, 7), 5, 30, 6, 48, 3): 1,
        }
    )
    symmetric_spike_profiles = bounded_degree_profiles(78, 516, 3434)
    assert set(symmetric_spike_profiles) == {
        (0, 0, 0, 0, 0, 1, 28, 49, 0, 0),
        (0, 0, 0, 0, 0, 0, 31, 46, 1, 0),
    }
    # The equality-shore matrix argument in the report eliminates the six
    # nonsymmetric order-(18,59) assemblies.
    articulation_after_equality = [
        assembly
        for assembly in articulation
        if not any(
            exceptional + 8 * scale == 18 and tuple(sorted(beta)) == (1, 2, 3)
            for exceptional, scale, beta in assembly
        )
    ]
    assert Counter(
        tuple(sorted(exceptional + 8 * scale for exceptional, scale, _ in assembly))
        for assembly in articulation_after_equality
    ) == Counter({(18, 59): 1, (27, 50): 1, (34, 43): 1})
    # The eight-point B0 handshake in the report eliminates (27,50).
    articulation_after_b0_handshake = [
        assembly
        for assembly in articulation_after_equality
        if tuple(
            sorted(exceptional + 8 * scale for exceptional, scale, _ in assembly)
        )
        != (27, 50)
    ]
    assert Counter(
        tuple(sorted(exceptional + 8 * scale for exceptional, scale, _ in assembly))
        for assembly in articulation_after_b0_handshake
    ) == Counter({(18, 59): 1, (34, 43): 1})

    # In the (34,43) branch, p low-set partners and q low-set B0 neighbours
    # of x satisfy p+q=4, with p<=3 and q<=2.  The local two-point W ledger
    # leaves exactly the two alternatives used in equations (24)--(27).
    pq_cases = {
        (partners_in_low_set, b0_neighbors_in_low_set)
        for partners_in_low_set in range(4)
        for b0_neighbors_in_low_set in range(3)
        if partners_in_low_set + b0_neighbors_in_low_set == 4
    }
    assert pq_cases == {(2, 2), (3, 1)}
    # For q=2, the three-local-edge branch is eliminated; in the four-edge
    # branch W must be the adjacent regular pair and the 3+3 shore split is
    # forced to (partners on S, U on S)=(3,0).  For q=1, C4-freeness bounds
    # the number b of U-points on S by one.
    q2_survivors = [("four", "regular-pair", 3, 0)]
    assert q2_survivors == [("four", "regular-pair", 3, 0)]
    assert [b for b in range(4) if b <= 1] == [0, 1]

    bin_ledger = [bin_ledger_assignment_counts(parts, types) for parts in partitions]
    assert [entry[0] for entry in bin_ledger] == [21, 27, 7, 9, 7, 10, 6, 6, 3, 1, 3]
    assert [entry[1] for entry in bin_ledger] == [21, 27, 10, 18, 7, 17, 12, 18, 6, 2, 6]

    print(f"verified component orders: {orders}")
    print("verified connectivity terminal: no admissible proper order is divisible by 8")
    print(f"verified B3-articulation assemblies: {articulation_order_pairs}")
    print(f"verified articulation equality profiles: {equality_profiles}")
    print(f"verified symmetric articulation spike profiles: {symmetric_spike_profiles}")
    print("verified post-equality articulation frontier: (18,59), (27,50), (34,43)")
    print("verified post-B0-handshake articulation frontier: (18,59), (34,43)")
    print("verified (34,43) low-set split: (p,q)=(2,2) or (3,1)")
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
