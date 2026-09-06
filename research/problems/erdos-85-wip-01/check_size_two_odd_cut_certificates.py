#!/usr/bin/env python3
"""Direct exact certificates separating the banked fractional witnesses.

No optimizer, cut-tree package, or external dependencies are needed.
"""

import json
from fractions import Fraction
from pathlib import Path


CERTIFICATES = [
    (12, (0, 10), {3, 5, 7, 13, 15, 19, 21}, Fraction(851, 1798)),
    (16, (0, 1), {4, 8, 10, 12, 14, 18, 22, 24, 26, 28, 30},
     Fraction(43324984, 278573383)),
    (16, (0, 12), {0, 10, 24}, Fraction(221067650, 278573383)),
]


def column(model, selected):
    size = 2 * model["q"]
    values = {}
    for orbit in model["orbits"]:
        weight = Fraction(orbit["value"])
        for sign in (-1, 1):
            for shift in range(size):
                a, b = [frozenset((sign * x + shift) % size for x in edge)
                        for edge in orbit["edges"]]
                if a == selected or b == selected:
                    other = b if a == selected else a
                    assert other != selected and len(other) == 2
                    assert other not in values or values[other] == weight
                    values[other] = weight
    return values


def check(model, edge, shore, expected):
    q = model["q"]
    selected = frozenset(edge)
    holes = {(a + step) % (2 * q) for a in selected for step in (-1, 1)}
    support = set(range(2 * q)) - holes
    assert len(holes) == 4 and shore <= support and len(shore) % 2 == 1
    weights = column(model, selected)
    def selector(pair):
        a, b = sorted(pair)
        difference = (b - a) % (2 * q)
        return (difference not in (0, 2, 2 * q - 2, q)
                and (difference % 2 == 0 or difference in (1, 2 * q - 1)))
    assert selector(selected) and all(selector(pair) for pair in weights)
    assert all(pair <= support and 0 < weight <= 1
               for pair, weight in weights.items())
    for vertex in support:
        assert sum((w for pair, w in weights.items() if vertex in pair), Fraction()) == 1
    cut = sum((w for pair, w in weights.items() if len(pair & shore) == 1), Fraction())
    internal = sum((w for pair, w in weights.items() if pair <= shore), Fraction())
    assert cut == expected and cut < 1
    assert 2 * internal + cut == len(shore)
    assert internal > (len(shore) - 1) // 2
    return dict(q=q, column=list(edge), odd_shore=sorted(shore),
                cut=str(cut), internal_weight=str(internal),
                matching_internal_limit=(len(shore) - 1) // 2)


if __name__ == "__main__":
    path = Path(__file__).with_name("size_two_symmetric_fractional_witnesses.json")
    models = {m["q"]: m for m in json.loads(path.read_text())}
    for q, edge, shore, expected in CERTIFICATES:
        print(check(models[q], edge, shore, expected))
