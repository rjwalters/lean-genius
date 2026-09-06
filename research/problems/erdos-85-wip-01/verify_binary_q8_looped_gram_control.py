#!/usr/bin/env python3
"""Published modular ruler gives a looped, invertible q8 Gram control.

This is not a simple-graph counterexample to A-REG: the six diagonal ones
are essential. No graph enumeration or external package is used.
"""

from collections import Counter

Q = 8
N = 64
RULER = {0, 4, 5, 17, 19, 25, 28, 35}
DEFECT_SHIFTS = {22, 26, 27, 32, 37, 38, 42}
LOOPS = [0, 2, 14, 32, 34, 46]


def determinant(matrix):
    """Fraction-free elimination, checking every exact division."""
    a = [row[:] for row in matrix]
    sign = previous = 1
    for k in range(len(a) - 1):
        if a[k][k] == 0:
            pivot = next((i for i in range(k + 1, len(a)) if a[i][k]), None)
            if pivot is None:
                return 0
            a[k], a[pivot] = a[pivot], a[k]
            sign = -sign
        p = a[k][k]
        for i in range(k + 1, len(a)):
            for j in range(k + 1, len(a)):
                value = p * a[i][j] - a[i][k] * a[k][j]
                quotient, remainder = divmod(value, previous)
                assert remainder == 0
                a[i][j] = quotient
            a[i][k] = 0
        previous = p
    return sign * a[-1][-1]


def main():
    differences = Counter((x-y) % N for x in RULER for y in RULER if x != y)
    assert len(RULER) == Q
    assert len(differences) == Q * (Q-1)
    assert set(differences.values()) == {1}
    assert set(range(1, N)) - differences.keys() == DEFECT_SHIFTS
    a = [[int((i+j) % N in RULER) for j in range(N)] for i in range(N)]
    assert all(a[i][j] == a[j][i] for i in range(N) for j in range(N))
    assert all(sum(row) == Q for row in a)
    assert [i for i in range(N) if a[i][i]] == LOOPS
    d = [[int((j-i) % N in DEFECT_SHIFTS) for j in range(N)]
         for i in range(N)]
    assert all(d[i][i] == 0 and sum(d[i]) == Q-1 for i in range(N))
    assert all(d[i][j] == d[j][i] for i in range(N) for j in range(N))
    for i in range(N):
        for j in range(N):
            square = sum(a[i][k]*a[k][j] for k in range(N))
            assert square == (Q-1)*int(i == j) + 1 - d[i][j]
            if i != j:
                assert square <= 1
    # A Hamiltonian cycle of step 27 proves D connected.
    cycle = [(27*i) % N for i in range(N)]
    assert len(set(cycle)) == N
    assert all(d[cycle[i]][cycle[(i+1) % N]] for i in range(N))
    odd_cycle = [0, 27, 54, 12, 38]
    assert len(set(odd_cycle)) == 5
    assert all(d[odd_cycle[i]][odd_cycle[(i+1) % 5]] for i in range(5))
    det = determinant(a)
    assert det == 490601813190770188069153280
    # Removing loops lowers precisely those six row degrees to seven.
    assert Counter(sum(a[i])-a[i][i] for i in range(N)) == {7: 6, 8: 58}
    print('verified: 56 distinct ordered ruler differences modulo64')
    print('verified: symmetric 0/1 matrix, row sum8, six diagonal ones')
    print('verified: A²=7I+J-D; D connected, nonbipartite, 7-regular')
    print('verified: det(A)=', det)
    print('therefore A² is rationally congruent to I64; this is NOT a loopless A-REG graph')


if __name__ == '__main__':
    main()
