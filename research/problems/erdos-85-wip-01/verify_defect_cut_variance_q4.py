#!/usr/bin/env python3
"""Exhaust the q=4 control for the defect cut-variance theorem.

This is an external consistency check, not a proof or finite endpoint.
It verifies all 2^16 shores of the banked fixed-free control, including the
two zero cuts coming from its disconnected defect graph.
"""

from itertools import combinations

from binary_q4_fixed_free_disconnected_control import A_EDGES, N, Q, adjacency


def main() -> None:
    a = adjacency(A_EDGES)
    d_edges = {
        (x, y)
        for x, y in combinations(range(N), 2)
        if not (a[x] & a[y])
    }
    d = adjacency(d_edges)

    minimum_nonzero_cut = None
    q_divisible_shores = 0
    support_checks = 0

    for mask in range(1 << N):
        shore = {v for v in range(N) if mask >> v & 1}
        s = len(shore)
        b = [len(a[v] & shore) for v in range(N)]
        cut = sum(1 for x, y in d_edges if (x in shore) != (y in shore))

        # Multiply the variance identity by q^2 to keep it integral.
        scaled_variance = sum((Q * degree - s) ** 2 for degree in b)
        assert scaled_variance == Q * Q * cut

        _, r = divmod(s, Q)
        assert cut >= r * (Q - r)
        if r == 0:
            assert cut % 2 == 0
            q_divisible_shores += 1

        if cut:
            minimum_nonzero_cut = (
                cut if minimum_nonzero_cut is None
                else min(minimum_nonzero_cut, cut)
            )

        # Check the support argument exactly on every q-divisible nonzero cut.
        if r == 0 and cut:
            level = s // Q
            y = [degree - level for degree in b]
            assert sum(y) == 0
            assert sum(value * value for value in y) == cut
            support = {v for v, value in enumerate(y) if value}
            m = len(support)
            assert 2 <= m <= cut

            ay = [sum(y[u] for u in a[v]) for v in range(N)]
            lay = []
            for v in range(N):
                if v in shore:
                    lay.append(len(d[v] - shore))
                else:
                    lay.append(-len(d[v] & shore))
            assert ay == lay

            ay_support = sum(value != 0 for value in ay)
            assert ay_support >= m * (Q - m + 1)
            assert ay_support <= 2 * cut
            support_checks += 1

    assert minimum_nonzero_cut == Q - 1
    print(f"verified all {1 << N} shores of the q={Q} control")
    print(f"minimum nonzero D-cut = {minimum_nonzero_cut} = q-1")
    print(f"q-divisible shores checked = {q_divisible_shores}")
    print(f"nonzero support-inequality checks = {support_checks}")


if __name__ == "__main__":
    main()
