#!/usr/bin/env python3
"""Verify an integral reciprocal cross block and its explicit C4 failure."""

import json
from itertools import combinations
from pathlib import Path


def check(model: dict) -> dict:
    q = model["q"]
    assert q == 16
    size, n = 2 * q, q - 2
    d_steps = (set(range(1, size, 2)) - {1, size - 1}) | {q}
    l_steps = set(range(1, size)) - d_steps - {2, size - 2}
    edges = [(a, b) for a in range(size) for b in range(a + 1, size)
             if (b - a) % size in l_steps]
    index = {e: i for i, e in enumerate(edges)}
    t = [set() for _ in edges]
    for orbit in model["translation_orbits"]:
        assert len(orbit) == 2 and all(len(e) == 2 for e in orbit)
        for shift in range(size):
            e, f = [tuple(sorted((a + shift) % size for a in g)) for g in orbit]
            i, j = index[e], index[f]
            assert i != j
            t[i].add(j)
            t[j].add(i)
    assert len(edges) == q * n
    for i, e in enumerate(edges):
        assert i not in t[i] and len(t[i]) == n
        assert all(i in t[j] for j in t[i])
        covered = []
        for j in t[i]:
            covered.extend(edges[j])
        forbidden = {(a + s) % size for a in e for s in (-1, 1)}
        # Each column is an actual perfect matching on C minus four points.
        assert len(forbidden) == 4
        assert len(covered) == len(set(covered)) == 2 * n
        assert set(covered) == set(range(size)) - forbidden
        for a in range(size):
            hb = sum((a - b) % size in (1, size - 1) for b in e)
            bt = sum(a in edges[j] for j in t[i])
            assert hb + bt == 1
        # The F-Gram diagonal holds: B^tB contributes 2, T^2 contributes n.
        assert 2 + len(t[i]) == q
    # Verify translation invariance and construct the reflected witness.
    rotate = [index[tuple(sorted((a + 1) % size for a in e))] for e in edges]
    reflect = [index[tuple(sorted(-a % size for a in e))] for e in edges]
    for i in range(len(edges)):
        assert {rotate[j] for j in t[i]} == t[rotate[i]]
    reflected = [{reflect[j] for j in t[reflect[i]]} for i in range(len(edges))]
    for i, e in enumerate(edges):
        covered = [a for j in reflected[i] for a in edges[j]]
        forbidden = {(a + s) % size for a in e for s in (-1, 1)}
        assert len(covered) == len(set(covered)) == 2 * n
        assert set(covered) == set(range(size)) - forbidden
        assert all(i in reflected[j] for j in reflected[i])
    assert any(t[i] != reflected[i] for i in range(len(edges)))
    cycle = [index[tuple(e)] for e in model["c4"]]
    assert len(cycle) == len(set(cycle)) == 4
    assert all(cycle[(j + 1) % 4] in t[cycle[j]] for j in range(4))
    codegrees = [len(t[i] & t[j]) for i, j in combinations(range(len(edges)), 2)]
    assert max(codegrees) == 8
    assert sum(c > 1 for c in codegrees) == 4912
    # Incident selectors have no common T-neighbor, as the matching law implies.
    assert all(not (set(edges[i]) & set(edges[j])) or not (t[i] & t[j])
               for i, j in combinations(range(len(edges)), 2))
    # Direct defect-triangle projection tests cannot see these opposite pairs.
    def cross_defect_count(i, j):
        return sum((a - b) % size in d_steps for a in edges[i] for b in edges[j])

    histogram = [0] * 5
    unseen_cycle_pairs = 0
    for i, j in combinations(range(len(edges)), 2):
        common = t[i] & t[j]
        if len(common) <= 1:
            continue
        r = cross_defect_count(i, j)
        histogram[r] += 1
        if r == 0:
            unseen_cycle_pairs += sum(cross_defect_count(a, b) == 0
                                      for a, b in combinations(common, 2))
    assert histogram == [1312, 672, 1056, 736, 1136]
    # Each four-cycle is counted once for each of its two opposite pairs.
    assert unseen_cycle_pairs == 2 * 720
    unseen = [index[e] for e in ((0, 4), (20, 24), (2, 14), (0, 28))]
    assert len(set(unseen)) == 4
    assert all(unseen[(j + 1) % 4] in t[unseen[j]] for j in range(4))
    assert cross_defect_count(unseen[0], unseen[2]) == 0
    assert cross_defect_count(unseen[1], unseen[3]) == 0
    # The incident-selector transition 2-factors also have no short cycles.
    transition = [{j for j in t[i] if set(e) & set(edges[j])}
                  for i, e in enumerate(edges)]
    cycle_lengths = []
    for parity in (0, 1):
        remaining = {i for i, e in enumerate(edges) if e[0] % 2 == e[1] % 2 == parity}
        lengths = []
        while remaining:
            seed = min(remaining)
            seen, pending = {seed}, [seed]
            while pending:
                vertex = pending.pop()
                assert len(transition[vertex]) == 2
                for other in transition[vertex] - seen:
                    seen.add(other)
                    pending.append(other)
            assert seen <= remaining
            remaining -= seen
            lengths.append(len(seen))
        assert sorted(lengths) == [8, 8, 16, 32, 32]
        cycle_lengths.append(sorted(lengths))
    assert all(not transition[i] for i, e in enumerate(edges) if e[0] % 2 != e[1] % 2)
    return dict(q=q, labels=len(edges), translation_orbits=len(model["translation_orbits"]),
                exact_cross_entries=size * len(edges), integral=True, symmetric=True,
                column_perfect_matchings=True, exterior_gram_diagonal=True,
                max_codegree=max(codegrees), exterior_common_neighbor_cap=False,
                transition_cycle_lengths=cycle_lengths,
                explicit_c4=model["c4"],
                collision_pairs_by_cross_defect_count=histogram,
                cycles_unseen_by_direct_triangle_projections=unseen_cycle_pairs // 2)


if __name__ == "__main__":
    witness = Path(__file__).with_name("size_two_integral_cross_block_q16.json")
    print(check(json.loads(witness.read_text())))
