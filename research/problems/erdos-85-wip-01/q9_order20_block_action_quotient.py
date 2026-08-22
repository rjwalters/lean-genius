#!/usr/bin/env python3
"""Enumerate the component-action quotient for q=9 order-20x4 shadows.

The internal-edge sieve forces all four block triples to have weight 20.
This script independently enumerates the transitive subgroups of S4 up to
conjugacy and records the point-stabilizer orbits on the other three blocks.
For an orbit of s incident block triples, transitivity inside the fixed
20-point component forces every point to occur in exactly s of their lines.
"""

from __future__ import annotations

from itertools import permutations, product


Permutation = tuple[int, ...]
IDENTITY = tuple(range(4))
S4 = tuple(permutations(range(4)))


def compose(left: Permutation, right: Permutation) -> Permutation:
    return tuple(left[right[index]] for index in range(4))


def inverse(permutation: Permutation) -> Permutation:
    result = [0] * 4
    for source, target in enumerate(permutation):
        result[target] = source
    return tuple(result)


def generated(generators: tuple[Permutation, ...]) -> frozenset[Permutation]:
    group = {IDENTITY}
    frontier = [IDENTITY]
    while frontier:
        element = frontier.pop()
        for generator in generators:
            image = compose(generator, element)
            if image not in group:
                group.add(image)
                frontier.append(image)
    return frozenset(group)


def conjugate_group(group: frozenset[Permutation], by: Permutation):
    by_inverse = inverse(by)
    return frozenset(compose(compose(by, element), by_inverse) for element in group)


def point_stabilizer_orbits(group: frozenset[Permutation]) -> tuple[int, ...]:
    stabilizer = frozenset(element for element in group if element[0] == 0)
    unseen = {1, 2, 3}
    sizes = []
    while unseen:
        seed = min(unseen)
        block_orbit = {element[seed] for element in stabilizer}
        unseen -= block_orbit
        sizes.append(len(block_orbit))
    return tuple(sorted(sizes))


def main() -> None:
    # Every subgroup of S4 is two-generated.  Deduplicate the generated
    # subgroups, retain the transitive ones, then quotient by S4 conjugacy.
    subgroups = {generated(pair) for pair in product(S4, repeat=2)}
    transitive = {
        group for group in subgroups if {element[0] for element in group} == set(range(4))
    }
    unseen = set(transitive)
    representatives = []
    while unseen:
        group = min(unseen, key=lambda item: (len(item), sorted(item)))
        conjugacy_class = {conjugate_group(group, element) for element in S4}
        unseen -= conjugacy_class
        representatives.append((group, len(conjugacy_class)))
    representatives.sort(key=lambda item: (len(item[0]), point_stabilizer_orbits(item[0])))

    profile = [
        (len(group), class_size, point_stabilizer_orbits(group))
        for group, class_size in representatives
    ]
    assert profile == [
        (4, 1, (1, 1, 1)),  # V4
        (4, 3, (1, 1, 1)),  # C4
        (8, 3, (1, 2)),     # D8
        (12, 1, (3,)),      # A4
        (24, 1, (3,)),      # S4
    ]
    print(f"transitive_subgroup_classes={len(profile)}")
    for order, class_size, stabilizer_orbits in profile:
        print(
            f"order={order}",
            f"conjugates={class_size}",
            f"incident_triple_orbits={stabilizer_orbits}",
            f"point_incidence_per_orbit={stabilizer_orbits}",
        )
    print("regular_actions point_incidence_per_incident_triple=1")


if __name__ == "__main__":
    main()
