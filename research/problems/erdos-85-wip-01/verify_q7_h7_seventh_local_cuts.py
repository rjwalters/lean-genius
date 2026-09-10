"""Exact dual certificates for five fixed-psi7 local cuts; no optimizer."""
from fractions import Fraction as F
import json
from pathlib import Path

BASE = Path(__file__).parent
FACTORS = [(-1, -5), (0, -7), (0, -6), (0, -3),
           (1, -7), (1, -5), (1, -3)]
Q = [[F(7), F(7)], [F(-1), F(0)]]
GI = [[F(98, 980), F(-56, 980)], [F(-56, 980), F(42, 980)]]


def matmul(a, b):
    return [[sum(x*y for x, y in zip(row, col))
             for col in zip(*b)] for row in a]


def nonnegative_at_roots(poly, b, c):
    """Reduce to A*x+B and check its minimum at both quadratic roots."""
    rem = list(poly)
    for j in range(len(rem)-1, 1, -1):
        rem[j-1] -= b*rem[j]
        rem[j-2] -= c*rem[j]
    a, constant = rem[1], rem[0]
    center = constant-a*b/2
    assert center >= 0 and center**2 >= a*a*(b*b-4*c)/4


def targets(t, tau, overlap, delta):
    row = [[F(1), F(t)]]
    q = []
    for _ in range(8):
        q.append(matmul(matmul(row, GI), [[F(1)], [F(t)]])[0][0])
        row = matmul(row, Q)
    z = F(t*(7-t), 49)
    m = [1-q[0]-z, -q[1], 7-t-q[2], 2*tau-q[3],
         (7-t)*(13-t)-7-q[4]]
    m.append(overlap+12*m[3]-36*m[1]-q[3]+2*q[2]-q[1])
    m.append(216*m[0]-108*m[2]+18*m[4]+q[3]-3*q[2]+3*q[1]-q[0]-z-2*delta)
    return m, q[7]


def main():
    witness = json.loads((BASE/'q7_h7_seventh_local_cuts.json').read_text())
    assert witness['h'] == 7
    expected = {(0, 2, 4, 1): 8212, (0, 2, 4, 7): 8226,
                (0, 3, 4, 3): 8440, (1, 2, 0, 5): 5712,
                (1, 2, 2, 6): 5750}
    seen = set()
    for cut in witness['cuts']:
        typ = tuple(cut[k] for k in ['t', 'tau', 'R', 'delta'])
        assert typ in expected and typ not in seen
        seen.add(typ)
        t, tau, overlap, delta = typ
        assert int(t == 0) <= tau <= 3-t
        assert overlap % 2 == 0 and 0 <= overlap <= 2*[0, 0, 1, 3, 4, 6][t+2*tau-1]
        assert 0 <= delta <= (6-t)*(5-t)//2
        m, q7 = targets(*typ)
        assert len(cut['duals']) == 2
        bounds = []
        for sign, data in zip([1, -1], cut['duals']):
            dual = list(map(F, data))
            assert len(dual) == 7
            poly = [-v for v in dual]+[F(sign)]
            for b, c in FACTORS:
                nonnegative_at_roots(poly, b, c)
            bounds.append(q7+sign*sum(a*b for a, b in zip(dual, m)))
        lower, upper = bounds
        assert lower == F(cut['lower']) and upper == F(cut['upper'])
        even = expected[typ]
        assert cut['even_floor'] == even and even % 2 == 0
        assert even < lower <= upper < even+2
        print('PASS', typ, ':', even, '< full C7 diagonal <', even+2)
    assert seen == set(expected)
    print('Five fixed-polynomial local types excluded; no full polynomial/profile exclusion.')


if __name__ == '__main__':
    main()
