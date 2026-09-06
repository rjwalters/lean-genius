#!/usr/bin/env python3
"""Exactly verify fractional cross-block witnesses; no optimizer is needed."""

import json
from fractions import Fraction
from pathlib import Path


def check(model: dict) -> dict:
    q = model["q"]
    assert isinstance(q, int) and q >= 8 and q % 2 == 0
    size, n = 2 * q, q - 2
    vertices = range(size)
    h = [{(a - 1) % size, (a + 1) % size} for a in vertices]
    d_steps = (set(range(1, size, 2)) - {1, size - 1}) | {q}
    l_steps = set(range(1, size)) - d_steps - {2, size - 2}
    edges = [(a, b) for a in vertices for b in range(a + 1, size)
             if (b - a) % size in l_steps]
    edge_index = {edge: i for i, edge in enumerate(edges)}
    incidence = [{i for i, edge in enumerate(edges) if a in edge}
                 for a in vertices]
    assert len(edges) == q * n
    assert all(len(row) == n for row in incidence)
    # Independently check the C-shore diagonal Gram equation.
    for a in vertices:
        for b in vertices:
            lhs = len(h[a] & h[b]) + len(incidence[a] & incidence[b])
            rhs = (q - 1) * (a == b) + 1 - ((b - a) % size in d_steps)
            assert lhs == rhs

    t = [{} for _ in edges]
    # Expand every recorded orbit, without the generator's canonicalization.
    for orbit in model["orbits"]:
        e, f = orbit["edges"]
        assert len(e) == len(f) == 2
        value = Fraction(orbit["value"])
        assert 0 < value <= 1
        for sign in (-1, 1):
            for shift in vertices:
                ee = tuple(sorted((sign * a + shift) % size for a in e))
                ff = tuple(sorted((sign * a + shift) % size for a in f))
                i, j = edge_index[ee], edge_index[ff]
                assert i != j
                for left, right in ((i, j), (j, i)):
                    if right in t[left]:
                        assert t[left][right] == value
                    t[left][right] = value

    deficits = []
    for i, e in enumerate(edges):
        assert i not in t[i]
        assert all(t[j].get(i) == value for j, value in t[i].items())
        assert sum(t[i].values(), Fraction()) == n
        # Symmetry makes row i also column i. Check every entry of BT.
        bt = [Fraction() for _ in vertices]
        for j, value in t[i].items():
            for a in edges[j]:
                bt[a] += value
        for a in vertices:
            hb = sum(b in h[a] for b in e)
            assert hb + bt[a] == 1
        deficit = n - sum((value * value for value in t[i].values()), Fraction())
        assert deficit == sum((value * (1 - value) for value in t[i].values()), Fraction())
        assert deficit >= 0
        deficits.append(deficit)
    # These particular witnesses fail the F-Gram diagonal in every row.
    assert all(value > 0 for value in deficits)
    return dict(q=q, exterior_labels=len(edges), nonzero_orbits=len(model["orbits"]),
                checked_cross_entries=size * len(edges),
                symmetric=True, exact_cross_block=True, exterior_gram_diagonal=False)


if __name__ == "__main__":
    path = Path(__file__).with_name("size_two_symmetric_fractional_witnesses.json")
    models = json.loads(path.read_text())
    assert [model["q"] for model in models] == [12, 16]
    for witness in models:
        print(check(witness))
