#!/usr/bin/env python3
"""Calibrate the primitive-cycle formula; uniform inequalities are in the note.

Uses exact integers/Fractions, the actual q4 graph, and the already-rejected
q16 ledger. Does not enumerate spectra or prove A-REG. Standard library only.
"""

from fractions import Fraction
from pathlib import Path
import runpy


def mobius(n):
    result, prime = 1, 2
    while prime * prime <= n:
        if n % prime == 0:
            n //= prime
            result = -result
            if n % prime == 0:
                return 0
        prime += 1
    return -result if n > 1 else result


def spectral_traces(n, degree, moment, limit):
    previous, current = [2], [0, 1]
    traces = [0]  # index zero is unused, not the trace of H^0
    for length in range(1, limit + 1):
        traces.append(sum(c * moment(i) for i, c in enumerate(current))
                      + (n * degree // 2 - n) * (1 + (-1)**length))
        following = [0] + current
        for i, c in enumerate(previous):
            following[i] -= (degree - 1) * c
        previous, current = current, following
    return traces


def primitive_count(traces, length):
    return Fraction(sum(mobius(length // j) * traces[j]
                        for j in range(1, length + 1) if length % j == 0),
                    2 * length)


def direct_hashimoto_traces(rows, limit):
    edges = [(u, v) for u, row in enumerate(rows) for v in row]
    index = {edge: i for i, edge in enumerate(edges)}
    successors = [[index[v, w] for w in rows[v] if w != u] for u, v in edges]
    traces = [0] * (limit + 1)
    for start in range(len(edges)):
        counts = [0] * len(edges)
        counts[start] = 1
        for length in range(1, limit + 1):
            following = [0] * len(edges)
            for i, count in enumerate(counts):
                for j in successors[i]:
                    following[j] += count
            counts = following
            traces[length] += counts[start]
    return traces


def adjacency_moments(rows, limit):
    n = len(rows)
    power = [[int(i == j) for j in range(n)] for i in range(n)]
    moments = [n]
    for _ in range(limit):
        power = [[sum(power[i][h] for h in rows[j]) for j in range(n)]
                 for i in range(n)]
        moments.append(sum(power[i][i] for i in range(n)))
    return moments


def main():
    base = Path(__file__).parent
    control = runpy.run_path(str(base / "binary_q4_fixed_free_disconnected_control.py"))
    rows = control["adjacency"](control["A_EDGES"])
    assert len(rows) == 16
    assert all(len(row) == 4 and u not in row for u, row in enumerate(rows))
    assert all(u in rows[v] for u, row in enumerate(rows) for v in row)
    assert all(len(set(rows[u]) & set(rows[v])) <= 1
               for u in range(16) for v in range(u))
    moments = adjacency_moments(rows, 12)
    spectral = spectral_traces(16, 4, lambda k: moments[k], 12)
    assert spectral == direct_hashimoto_traces(rows, 12)
    counts = [primitive_count(spectral, k) for k in range(1, 13)]
    assert all(value >= 0 and value.denominator == 1 for value in counts)
    assert counts[2:8] == [8, 0, 24, 100, 144, 394]
    print("q4: direct Hashimoto and spectral traces agree at lengths 1..12 PASS")
    print("q4 primitive counts at lengths 3..8:", [str(c) for c in counts[2:8]])

    ledger = runpy.run_path(str(base / "verify_nonbip_connected_odd_power_mod4.py"))
    traces = spectral_traces(256, 16, ledger["moment"], 20)
    counts = [primitive_count(traces, k) for k in range(1, 21)]
    assert all(value >= 0 for value in counts)
    assert [k for k, value in enumerate(counts, 1) if value.denominator != 1] == [6, 12]
    assert counts[2:8] == [641, 0, 75606, Fraction(2157713, 2), 12200814, 159517689]
    print("q16: nonnegativity through 20 PASS; integrality FAIL at lengths 6,12")
    print("q16 primitive counts at lengths 3..8:", [str(c) for c in counts[2:8]])
    print("These calibrations do not establish a new spectrum exclusion or A-REG.")


if __name__ == "__main__":
    main()
