#!/usr/bin/env python3
"""Audit the routing 1-factorizations in the checked Boza q=7 witness.

The six fibers are ``(v // 2) mod 6``.  Each doubled fiber block is the
disjoint union of two even cycles and therefore has four decompositions into
two perfect matchings.  We enumerate all 4^3 choices, form the eight routing
permutations for every fiber pair, and test whether each factorization is a
coset of a regular permutation group (in particular, a cyclic Singer action).
"""

from __future__ import annotations

import itertools
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
WITNESS = ROOT / "proofs/Proofs/Erdos85Boza48Witness.lean"


def compose(p: tuple[int, ...], q: tuple[int, ...]) -> tuple[int, ...]:
    """Return p after q."""
    return tuple(p[q[x]] for x in range(len(p)))


def inverse(p: tuple[int, ...]) -> tuple[int, ...]:
    ans = [0] * len(p)
    for x, y in enumerate(p):
        ans[y] = x
    return tuple(ans)


def permutation_order(p: tuple[int, ...]) -> int:
    seen = set()
    order = 1
    for x in range(len(p)):
        if x in seen:
            continue
        n, y = 0, x
        while y not in seen:
            seen.add(y)
            n += 1
            y = p[y]
        order = order * n // __import__("math").gcd(order, n)
    return order


def load_graph() -> list[set[int]]:
    text = WITNESS.read_text()
    body = text.split("def boza48Edges", 1)[1].split("]", 1)[0]
    edges = [tuple(map(int, pair)) for pair in re.findall(r"\((\d+),\s*(\d+)\)", body)]
    adj = [set() for _ in range(48)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    assert len(edges) == 168 and {len(ns) for ns in adj} == {7}
    return adj


def alternating_decompositions(
    left: list[int], right: list[int], adj: list[set[int]]
) -> list[tuple[tuple[int, ...], tuple[int, ...]]]:
    """All alternating two-colorings of a 2-regular bipartite block."""
    li, ri = {v: i for i, v in enumerate(left)}, {v: i for i, v in enumerate(right)}
    left_set, right_set = set(left), set(right)
    block = {v: sorted(adj[v] & (right_set if v in left_set else left_set)) for v in left + right}
    assert {len(block[v]) for v in block} == {2}
    unseen, cycles = set(left + right), []
    while unseen:
        start = min(unseen)
        cycle, prev, cur = [], None, start
        while True:
            cycle.append(cur)
            unseen.discard(cur)
            nxt = next(v for v in block[cur] if v != prev)
            prev, cur = cur, nxt
            if cur == start:
                break
        cycles.append(cycle)

    answers = []
    for phases in itertools.product((0, 1), repeat=len(cycles)):
        colors = [dict(), dict()]
        for cycle, phase in zip(cycles, phases):
            for t, u in enumerate(cycle):
                v = cycle[(t + 1) % len(cycle)]
                if u in li:
                    colors[(t + phase) % 2][li[u]] = ri[v]
                else:
                    colors[(t + phase) % 2][li[v]] = ri[u]
        pair = tuple(tuple(c[x] for x in range(8)) for c in colors)
        answers.append(pair)
    return answers


def normalized_group(
    perms: list[tuple[int, ...]],
) -> frozenset[tuple[int, ...]] | None:
    """Return the regular group underlying a factorization coset, if any."""
    ident = tuple(range(8))
    for base in perms:
        normalized = {compose(inverse(base), p) for p in perms}
        if ident not in normalized or len(normalized) != 8:
            continue
        if any(compose(p, q) not in normalized for p in normalized for q in normalized):
            continue
        if any(sum(p[x] == x for x in range(8)) for p in normalized if p != ident):
            continue
        return frozenset(normalized)
    return None


def group_type(perms: list[tuple[int, ...]]) -> str | None:
    """Classify a factorization as a regular-group coset, if possible."""
    group = normalized_group(perms)
    if group is None:
        return None
    orders = sorted(permutation_order(p) for p in group)
    return "cyclic" if 8 in orders else "regular-noncyclic:" + ",".join(map(str, orders))


def normalizes(p: tuple[int, ...], group: frozenset[tuple[int, ...]]) -> bool:
    pinv = inverse(p)
    return {compose(compose(p, h), pinv) for h in group} == set(group)


def main() -> None:
    adj = load_graph()
    fibers = [[v for v in range(48) if (v // 2) % 6 == i] for i in range(6)]
    loc = [{v: x for x, v in enumerate(fiber)} for fiber in fibers]

    internal = []
    blocks: dict[tuple[int, int], list[tuple[int, ...]]] = {}
    doubled = []
    for i in range(6):
        internal.append(tuple(loc[i][next(iter(adj[v] & set(fibers[i])))] for v in fibers[i]))
        for j in range(i + 1, 6):
            count = sum(v in adj[u] for u in fibers[i] for v in fibers[j])
            if count == 8:
                blocks[i, j] = [tuple(loc[j][next(iter(adj[u] & set(fibers[j])))] for u in fibers[i])]
            else:
                assert count == 16
                doubled.append((i, j))

    decompositions = [alternating_decompositions(fibers[i], fibers[j], adj) for i, j in doubled]
    assert sorted(doubled) == [(0, 3), (1, 4), (2, 5)]
    assert [len(ds) for ds in decompositions] == [4, 4, 4]

    verdict_hist: dict[tuple[int, int], dict[str, int]] = {
        (i, j): {} for i in range(6) for j in range(i + 1, 6)
    }
    simultaneous = {"all_group": 0, "all_cyclic": 0}
    successful_choices = []
    successful_group_counts = []
    successful_normalizer_counts = []
    for choice_indices in itertools.product(*(range(len(ds)) for ds in decompositions)):
        choices = [ds[index] for ds, index in zip(decompositions, choice_indices)]
        chosen = dict(blocks)
        chosen.update({pair: list(ms) for pair, ms in zip(doubled, choices)})

        def maps(i: int, j: int) -> list[tuple[int, ...]]:
            if i < j:
                return chosen[i, j]
            return [inverse(p) for p in chosen[j, i]]

        kinds, groups = [], []
        for i in range(6):
            for j in range(i + 1, 6):
                routes = []
                for k in range(6):
                    if k in (i, j):
                        continue
                    for ik in maps(i, k):
                        for jk in maps(j, k):
                            routes.append(compose(inverse(jk), ik))
                for ij in maps(i, j):
                    routes.append(compose(ij, internal[i]))
                    routes.append(compose(internal[j], ij))
                assert len(routes) == 8 and all(len(set(p[x] for p in routes)) == 8 for x in range(8))
                kind = group_type(routes) or "non-group"
                verdict_hist[i, j][kind] = verdict_hist[i, j].get(kind, 0) + 1
                kinds.append(kind)
                groups.append(normalized_group(routes))
        simultaneous["all_group"] += all(k != "non-group" for k in kinds)
        simultaneous["all_cyclic"] += all(k == "cyclic" for k in kinds)
        if all(k != "non-group" for k in kinds):
            successful_choices.append(choice_indices)
            successful_group_counts.append(len(set(groups)))
            group = groups[0]
            assert group is not None
            datum_perms = internal + [p for pair in sorted(chosen) for p in chosen[pair]]
            successful_normalizer_counts.append(
                (sum(normalizes(p, group) for p in datum_perms), len(datum_perms))
            )

    print("doubled_pairs", doubled)
    print("decomposition_choices", 4 ** 3)
    for pair, hist in verdict_hist.items():
        print("pair", pair, hist)
    print("simultaneous", simultaneous)
    print("successful_choices", successful_choices)
    print("distinct_coordinate_groups", successful_group_counts)
    print("datum_perms_in_common_normalizer", successful_normalizer_counts)


if __name__ == "__main__":
    main()
