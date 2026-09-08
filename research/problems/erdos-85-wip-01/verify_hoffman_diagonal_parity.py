#!/usr/bin/env python3
"""Exact calibration of the diagonal Hoffman obstruction; no Lean claim."""
from pathlib import Path
import runpy


def multiply_poly(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i+j] += x*y
    return out


def polynomial(factors):
    out = [1]
    for factor in factors:
        out = multiply_poly(out, factor)
    return out


def value(p, x):
    out = 0
    for c in reversed(p):
        out = out*x+c
    return out


def matmul(a, b):
    return [[sum(x*y for x, y in zip(row, col))
             for col in zip(*b)] for row in a]


def verify_graph(rows, q, h, name):
    n = len(rows)
    a = [[int(j in rows[i]) for j in range(n)] for i in range(n)]
    assert all(sum(row) == q for row in a)
    assert all(a[i][i] == 0 for i in range(n))
    assert all(a[i][j] == a[j][i] for i in range(n) for j in range(n))
    hp = [[0]*n for _ in range(n)]
    for c in reversed(h):
        hp = matmul(hp, a)
        for i in range(n):
            hp[i][i] += c
    assert value(h, q) % n == 0
    quotient = value(h, q)//n
    assert all(x == quotient for row in hp for x in row)
    if q % 2 == 0:
        power = [[int(i == j) for j in range(n)] for i in range(n)]
        for _ in range(12):
            power = matmul(power, a)
            assert all(power[i][i] % 2 == 0 for i in range(n))
        assert quotient % 2 == h[0] % 2
        if n % 2 == 0:
            assert quotient % 2 == 0
    print(f"{name}: exact matrix Hoffman identity, quotient={quotient}")
    return quotient


def main():
    h = polynomial([[4, 1], [2, 1], [-4, 1], [-2, 0, 1],
                    [-14, 0, 1], [-22, 0, 1]])
    assert h == [19712, 9856, -13392, -6696, 1976, 988,
                 -108, -54, 2, 1]
    assert value(h, 16) == 62136771840
    assert value(h, 16)//256 == 242721765
    assert value(h, 16) % 256 == 0 and value(h, 16) % 512 == 256
    print("q16 ledger: ordinary Hoffman divisibility PASS; 2n divisibility FAIL")
    base = Path(__file__).parent
    control = runpy.run_path(str(base / 'binary_q4_fixed_free_disconnected_control.py'))
    rows = control['adjacency'](control['A_EDGES'])
    h4 = polynomial([[0, 1], [2, 1], [-2, 0, 1], [14, 0, -8, 0, 1]])
    assert verify_graph(rows, 4, h4, 'actual q4') == 2982
    cycle = [{(i-1) % 6, (i+1) % 6} for i in range(6)]
    assert verify_graph(cycle, 2, polynomial([[2, 1], [-1, 0, 1]]), 'C6') == 2
    for n in [4, 5]:
        complete = [set(range(n)) - {i} for i in range(n)]
        assert verify_graph(complete, n-1, [1, 1], f'K{n}') == 1
    print("Actual controls PASS; K4/K5 retain required hypothesis boundaries.")
    print("The q16 spectrum is excluded; general A-REG remains open.")


if __name__ == '__main__':
    main()
