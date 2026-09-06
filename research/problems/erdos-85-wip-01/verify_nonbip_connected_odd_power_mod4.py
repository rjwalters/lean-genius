#!/usr/bin/env python3
"""Exact rejection of the q16 unpaired spectrum (squad #40388).

This is a necessary matrix congruence, not a general A-REG exclusion.
Only Python's standard library is needed.
"""

from pathlib import Path
import runpy


PAIRS = {2: 2, 10: 3, 12: 1, 14: 92, 18: 1,
         21: 22, 22: 1, 23: 1, 26: 1}


def moment(k):
    return (16**k + 4*(-4)**k + 2**k + 2*(-1)**k
            + (2*sum(c*a**(k//2) for a, c in PAIRS.items())
               if k % 2 == 0 else 0))


def multiply(a, b):
    return [[sum(x*y for x, y in zip(row, col))
             for col in zip(*b)] for row in a]


def verify_graph(rows, degree, name):
    n = len(rows)
    assert all(len(set(row)) == degree for row in rows)
    a = [[int(j in rows[i]) for j in range(n)] for i in range(n)]
    assert all(a[i][i] == 0 for i in range(n))
    assert all(a[i][j] == a[j][i] for i in range(n) for j in range(n))
    power = [[int(i == j) for j in range(n)] for i in range(n)]
    for m in range(1, 8):
        power = multiply(power, a)
        if m % 2:
            trace = sum(power[i][i] for i in range(n))
            trace_square = sum(x*x for row in power for x in row)
            assert all(power[i][i] % 2 == 0 for i in range(n))
            assert (trace_square + trace - n*degree**m) % 4 == 0
            if m == 3:
                print(f"{name}: trA3={trace}, trA6={trace_square}, PASS")


def main():
    assert moment(0) == 256
    assert [moment(k) for k in range(1, 7)] == [
        0, 4096, 3846, 126976, 1044510, 17807980]
    residue = (moment(6) + moment(3) - 256*16**3) % 4
    assert residue == 2

    # Independent AD calculation from the defect eigenvalue ledger.
    # Principal D root15; A roots -4,2,-1 give D roots -1,11,14.
    d3 = 15**3 + 4*(-1)**3 + 11**3 + 2*14**3
    d3 += sum(2*c*(15-a)**3 for a, c in PAIRS.items())
    assert d3 == 6036
    assert moment(6) == 16**6 + 256*15**2*18 - d3
    assert (moment(3)//6, d3//6) == (641, 1006)
    trace_ad = 256*16 - moment(3)
    norm_ad = 15*(256*15) + 256*15**2 - d3
    assert (trace_ad, norm_ad) == (250, 109164)
    assert (norm_ad - 256*16*15 + trace_ad) % 4 == 2
    print(f"q16 spectrum: residue={residue}; integer symmetric regular "
          "zero-diagonal realization EXCLUDED")

    base = Path(__file__).parent
    q4 = runpy.run_path(str(base / "binary_q4_fixed_free_disconnected_control.py"))
    rows4 = q4["adjacency"](q4["A_EDGES"])
    verify_graph(rows4, 4, "q4")
    h36 = runpy.run_path(str(base / "verify_boza_h36_triangle_control.py"))
    verify_graph(h36["ROWS"], 6, "H36")
    verify_graph([{1, 2}, {0, 2}, {0, 1}], 2, "triangle")
    verify_graph([{1}, {0}], 1, "single edge")
    print("Odd powers m=1,3,5,7 passed on all actual controls.")


if __name__ == "__main__":
    main()
