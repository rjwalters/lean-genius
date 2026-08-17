#!/usr/bin/env python3
"""Necessary branch-partition census for the q=8 square-order core.

This is a discovery calculation, not a proof certificate.  It enumerates the
77 high-incidence profiles allowed by the proved first and second moments,
then imposes the proved branchwise conservation law at every low vertex type.
The relaxation forgets adjacency and asks only for multiset partitions, so a
rejected profile is impossible while a surviving profile need not be realizable.
"""

from functools import lru_cache


Q = 8


def arithmetic_profiles():
    profiles = []
    for h in range(2, 13, 2):
        low_count = Q * Q - h
        for n0 in range(low_count + 1):
            for n1 in range(low_count - n0 + 1):
                for n2 in range(low_count - n0 - n1 + 1):
                    for n3 in range(low_count - n0 - n1 - n2 + 1):
                        n4 = low_count - n0 - n1 - n2 - n3
                        counts = (n0, n1, n2, n3, n4)
                        if sum(i * counts[i] for i in range(5)) != 9 * h:
                            continue
                        if sum(i * i * counts[i] for i in range(5)) != h * (h + Q):
                            continue
                        profiles.append((h, counts))
    return profiles


@lru_cache(maxsize=None)
def submultisets(counts, size, weight):
    answers = []

    def visit(i, remaining_size, remaining_weight, prefix):
        if i == 4:
            take = remaining_size
            if take <= counts[i] and i * take == remaining_weight:
                answers.append(tuple(prefix + [take]))
            return
        for take in range(min(counts[i], remaining_size) + 1):
            if i * take <= remaining_weight:
                visit(
                    i + 1,
                    remaining_size - take,
                    remaining_weight - i * take,
                    prefix + [take],
                )

    visit(0, size, weight, [])
    return tuple(answers)


def subtract(left, right):
    return tuple(x - y for x, y in zip(left, right))


def vertex_type_feasible(h, low_counts, k_u):
    # High vertices also have incidence weight zero; remove the chosen low u.
    available = list(low_counts)
    available[0] += h
    available[k_u] -= 1
    available = tuple(available)

    # k_u large branches: size q and weight h-k_u+q.
    # q-k_u small branches: size q-1 and weight h-k_u.
    # The remaining D-neighbors: size q-1-k_u and weight h-k_u, by
    # (D+I)k=h1.  Sorting only reduces dynamic-programming branching.
    groups = tuple(
        sorted(
            [(Q, h - k_u + Q)] * k_u
            + [(Q - 1, h - k_u)] * (Q - k_u)
            + [(Q - 1 - k_u, h - k_u)]
        )
    )

    @lru_cache(maxsize=None)
    def partition(counts, group_index):
        if group_index == len(groups):
            return all(count == 0 for count in counts)
        size, weight = groups[group_index]
        for chosen in submultisets(counts, size, weight):
            if partition(subtract(counts, chosen), group_index + 1):
                return True
        return False

    return partition(available, 0)


def main():
    profiles = arithmetic_profiles()
    assert len(profiles) == 77
    expected_initial = {2: 1, 4: 4, 6: 12, 8: 29, 10: 22, 12: 9}
    initial = {h: sum(profile_h == h for profile_h, _ in profiles) for h in expected_initial}
    assert initial == expected_initial

    survivors = []
    rejected = []
    for h, counts in profiles:
        bad_types = tuple(
            k for k, multiplicity in enumerate(counts)
            if multiplicity and not vertex_type_feasible(h, counts, k)
        )
        (rejected if bad_types else survivors).append((h, counts, bad_types))

    expected_survivors = {2: 1, 4: 3, 6: 7, 8: 18, 10: 19, 12: 4}
    survivor_counts = {
        h: sum(profile_h == h for profile_h, _, _ in survivors)
        for h in expected_survivors
    }
    assert len(rejected) == 25
    assert len(survivors) == 52
    assert survivor_counts == expected_survivors

    print(f"arithmetic profiles: {len(profiles)} {initial}")
    print(f"branch-partition survivors: {len(survivors)} {survivor_counts}")
    print(f"rejected profiles: {len(rejected)}")
    for h, counts, bad_types in rejected:
        print(f"h={h:2d} low_counts={counts} infeasible_k={bad_types}")


if __name__ == "__main__":
    main()
