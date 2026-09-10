"""Exact fixed-psi7 quadratic compression certificates; no optimizer."""
from fractions import Fraction as F
from itertools import combinations
import json
from pathlib import Path


SHAPES = [
    [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (2, 5), (3, 6), (4, 6), (5, 6)],
    [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (3, 6), (4, 5), (5, 6)],
]
FACTORS = [(-1, -5), (0, -7), (0, -6), (0, -3), (1, -7), (1, -5), (1, -3)]


def mul(a, b):
    return [[sum(x*y for x, y in zip(row, col)) for col in zip(*b)] for row in a]


def adjacency(edges):
    a = [[0]*7 for _ in range(7)]
    for u, v in edges:
        assert 0 <= u < v < 7 and not a[u][v]
        a[u][v] = a[v][u] = 1
    return a


def positive_definite(a):
    """Exact positive pivots of successive symmetric Schur complements."""
    a = [list(map(F, row)) for row in a]
    for k in range(len(a)):
        pivot = a[k][k]
        assert pivot > 0
        for i in range(k+1, len(a)):
            for j in range(k+1, len(a)):
                a[i][j] -= a[i][k]*a[k][j]/pivot


def main():
    witness = json.loads(Path(__file__).with_name('q7_h7_empty_compression_cuts.json').read_text())
    assert witness['polynomial'] == [223, -10, -25]
    # f modulo x²+b*x+c is (25b-10)*x+(223+25c).
    for b, c in FACTORS:
        slope, constant = F(25*b-10), F(223+25*c)
        center = constant-slope*b/2
        assert center > 0 and center*center > slope*slope*(b*b-4*c)/4

    gram = [[F(42), F(56)], [F(56), F(98)]]
    gi = [[F(98, 980), F(-56, 980)], [F(-56, 980), F(42, 980)]]
    q = [[F(7), F(7)], [F(-1), F(0)]]
    assert mul(gram, gi) == [[1, 0], [0, 1]]
    q0, q1, q2 = gi[0][0], mul(q, gi)[0][0], mul(mul(q, q), gi)[0][0]
    assert (q0, q1, q2) == (F(1, 10), F(3, 10), F(7, 5))
    assert 1-7*q0 > 0
    assert -10*(223*q0-10*q1-25*q2) == 157

    assert len(witness['shapes']) == 2
    total_excluded = 0
    for shape_index, (edges, data) in enumerate(zip(SHAPES, witness['shapes'])):
        assert data['shape'] == [list(e) for e in edges]
        a = adjacency(edges)
        a2 = mul(a, a)
        assert sorted(map(sum, a)) == [2, 2, 2, 3, 3, 3, 3]
        assert all(a2[i][j] <= 1 for i, j in combinations(range(7), 2))
        allowed = [(i, j) for i, j in combinations(range(7), 2) if a2[i][j] == 0]
        assert len(allowed) == 6 and data['allowed'] == [list(e) for e in allowed]
        assert [case['mask'] for case in data['cases']] == list(range(64))
        positive = []
        for case in data['cases']:
            mask = case['mask']
            x = adjacency([edge for k, edge in enumerate(allowed) if mask >> k & 1])
            c2 = [[a2[i][j]+(7-sum(a[i]) if i == j else 0)+x[i][j]
                   for j in range(7)] for i in range(7)]
            h = [[(2230 if i == j else 0)-100*a[i][j]-250*c2[i][j]+157
                  for j in range(7)] for i in range(7)]
            # The all-ones test alone forces at most three outside pairs.
            assert sum(map(sum, h)) == 1753-500*mask.bit_count()
            if case['status'] == 'positive_definite':
                positive_definite(h)
                positive.append(mask)
            else:
                assert case['status'] == 'excluded'
                v = case['vector']
                assert len(v) == 7 and all(type(n) is int for n in v)
                value = sum(v[i]*h[i][j]*v[j] for i in range(7) for j in range(7))
                assert value == case['quadratic_value'] and value < 0
                total_excluded += 1
        assert len(positive) == [26, 30][shape_index]
        assert all(mask.bit_count() <= 3 for mask in positive)
        assert sum(mask.bit_count() == 3 for mask in positive) == [4, 8][shape_index]
        assert all(mask in positive for mask in range(64) if mask.bit_count() <= 2)
        print('PASS shape', 'AB'[shape_index], ':', len(positive), 'positive definite,',
              64-len(positive), 'excluded by integer negative vectors')
    assert total_excluded == 72
    print('Fixed-psi7 necessary compression test only; no graph/profile/polynomial exclusion.')


if __name__ == '__main__':
    main()
