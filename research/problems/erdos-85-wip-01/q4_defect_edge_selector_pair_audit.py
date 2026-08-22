#!/usr/bin/env python3
"""Falsify the local T-boundary formula for defect-edge selector pairs."""

from __future__ import annotations

from collections import Counter
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path


def load_control():
    path = Path(__file__).with_name("binary_q4_fixed_free_disconnected_control.py")
    spec = spec_from_file_location("q4_control", path)
    assert spec is not None and spec.loader is not None
    module = module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main() -> None:
    control = load_control()
    adjacency = control.adjacency(control.A_EDGES)
    n = control.N
    common = [
        [len(adjacency[x] & adjacency[y]) for y in range(n)]
        for x in range(n)
    ]
    defect = [
        {y for y in range(n) if y != x and common[x][y] == 0}
        for x in range(n)
    ]
    triangle_free = [adjacency[x] & defect[x] for x in range(n)]
    patterns: Counter[tuple] = Counter()
    feature_degrees: dict[tuple, set[int]] = {}

    for u in range(n):
        for v in defect[u]:
            rows = {a: 0 for a in adjacency[u]}
            columns = {b: 0 for b in adjacency[v]}
            for z in range(n):
                if z in adjacency[u] or z in adjacency[v] or z in (u, v):
                    continue
                if z in defect[u] or z in defect[v]:
                    continue
                left = adjacency[u] & adjacency[z]
                right = adjacency[v] & adjacency[z]
                assert len(left) == len(right) == 1
                rows[next(iter(left))] += 1
                columns[next(iter(right))] += 1
            row_profile = tuple(sorted(
                (rows[a], int(a in triangle_free[u])) for a in adjacency[u]
            ))
            column_profile = tuple(sorted(
                (columns[b], int(b in triangle_free[v])) for b in adjacency[v]
            ))
            assert row_profile == column_profile
            patterns[(int(v in triangle_free[u]), row_profile, sum(rows.values()))] += 1
            for a, degree in rows.items():
                features = (
                    int(v in triangle_free[u]),
                    int(a == v),
                    int(a in triangle_free[u]),
                    int(a in adjacency[v]),
                    int(a in defect[v]),
                    common[a][v],
                )
                feature_degrees.setdefault(features, set()).add(degree)

    expected = Counter({
        (0, ((1, 0), (1, 0), (1, 0), (1, 0)), 4): 16,
        (0, ((1, 0), (1, 0), (2, 0), (2, 0)), 6): 8,
        (1, ((0, 1), (1, 0), (2, 0), (3, 1)), 6): 16,
        (0, ((1, 0), (1, 0), (2, 1), (2, 1)), 6): 8,
    })
    assert patterns == expected
    ambiguous = {key: value for key, value in feature_degrees.items()
                 if len(value) > 1}
    assert ambiguous
    assert any(value == {1, 2} for value in ambiguous.values())
    for pattern, count in sorted(patterns.items(), key=repr):
        print(f"count={count} pattern={pattern}")
    print(f"ambiguous_local_feature_classes={len(ambiguous)}")
    print("q4_defect_edge_selector_T_boundary_formula_falsified=True")


if __name__ == "__main__":
    main()
