#!/usr/bin/env python3
"""Exact q=4 calibration of the mod-2 Pfaffian/Plucker proposal.

For the banked fixed-point-free q=4 incidence matrix, compute every
submaximal Pfaffian over F_2.  The resulting Plucker bivector is exactly
1 wedge w, where w is the indicator of one deficiency component.  Thus the
cofactor package carries precisely the already-known second adjacency-kernel
shore and no additional incidence placement.
"""

from functools import cache

from binary_q4_fixed_free_disconnected_control import A_EDGES, N, adjacency


def main() -> None:
    neighbors = adjacency(A_EDGES)
    rows = [sum(1 << j for j in neighbors[i]) for i in range(N)]

    @cache
    def pfaffian(mask: int) -> int:
        """Pfaffian of the principal submatrix on mask, modulo two."""
        if mask == 0:
            return 1
        i_bit = mask & -mask
        i = i_bit.bit_length() - 1
        rest = mask ^ i_bit
        value = 0
        choices = rows[i] & rest
        while choices:
            j_bit = choices & -choices
            value ^= pfaffian(rest ^ j_bit)
            choices ^= j_bit
        return value

    full = (1 << N) - 1
    cofactors = {
        (i, j): pfaffian(full ^ (1 << i) ^ (1 << j))
        for i in range(N)
        for j in range(i + 1, N)
    }

    # Recover w by fixing w_0=0 and using p_0j=w_0+w_j.
    w = [0] + [cofactors[0, j] for j in range(1, N)]
    assert any(w) and not all(w)
    assert all(cofactors[i, j] == (w[i] ^ w[j]) for i, j in cofactors)

    # Both 1 and w are in ker(A); they span it in the exact control.
    assert all(sum(1 for j in neighbors[i]) % 2 == 0 for i in range(N))
    assert all(sum(w[j] for j in neighbors[i]) % 2 == 0 for i in range(N))
    kernel = [
        mask
        for mask in range(1 << N)
        if all((rows[i] & mask).bit_count() % 2 == 0 for i in range(N))
    ]
    w_mask = sum(bit << i for i, bit in enumerate(w))
    assert set(kernel) == {0, full, w_mask, full ^ w_mask}

    # The Plucker quadrics now reduce to the tautology for 1 wedge w.
    for i in range(N):
        for j in range(i + 1, N):
            for k in range(j + 1, N):
                for ell in range(k + 1, N):
                    assert (
                        cofactors[i, j] * cofactors[k, ell]
                        ^ cofactors[i, k] * cofactors[j, ell]
                        ^ cofactors[i, ell] * cofactors[j, k]
                    ) == 0

    shores = [i for i, bit in enumerate(w) if bit]
    assert len(shores) == 8
    print("verified q=4 Pfaffian/Plucker kernel collapse")
    print("corank_F2(A) = 2; p_ij = w_i + w_j; |supp(w)| = 8")


if __name__ == "__main__":
    main()
