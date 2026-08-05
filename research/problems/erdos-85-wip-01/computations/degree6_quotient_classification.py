#!/usr/bin/env python3
"""Classify degree-six defect-component quotients surviving the color trace.

For d=6 and n=33 the quotient Q and component lengths r satisfy

    Q 1 = 6 1,
    Q^2 = 3 I + 1 r^T,
    r_i Q_ij = r_j Q_ji.

Cycle parity gives an odd number of components and an even number of even
lengths.  The cubic color trace says that the total length of N-components is
0 modulo 3; an N-component has length at least five and Q_ii >= 2.

The search is exact integer backtracking, not SMT.  It first derives each row
domain from row sum, detailed balance, and the diagonal entry of Q^2, then
checks compatibility and the off-diagonal entries of Q^2.

The corrected search also applies the local antipodal-C5 obstruction.
"""

from functools import lru_cache


def compositions(total, length, prefix=()):
    if length == 1:
        yield prefix + (total,)
        return
    for value in range(total + 1):
        yield from compositions(total - value, length - 1, prefix + (value,))


def partitions(total, length, lower=3, prefix=()):
    if length == 0:
        if total == 0:
            yield prefix
        return
    for value in range(lower, total // length + 1):
        yield from partitions(
            total - value, length - 1, value, prefix + (value,)
        )


@lru_cache(None)
def degree_six_rows(length):
    return tuple(compositions(6, length))


def row_domain(lengths, index):
    order = lengths[index]
    answer = []
    for row in degree_six_rows(len(lengths)):
        reverse = []
        for j, other_order in enumerate(lengths):
            numerator = order * row[j]
            if numerator % other_order:
                break
            reverse.append(numerator // other_order)
        else:
            diagonal_square = sum(
                row[j] * reverse[j] for j in range(len(lengths))
            )
            if diagonal_square == order + 3:
                answer.append(row)
    return answer


def quotient_matrices(lengths):
    size = len(lengths)
    domains = [row_domain(lengths, i) for i in range(size)]
    order = sorted(range(size), key=lambda i: len(domains[i]))
    chosen = {}

    def search(position, diagonal_trace):
        if position == size:
            if diagonal_trace != 6:
                return
            matrix = tuple(chosen[i] for i in range(size))
            if all(
                sum(matrix[i][k] * matrix[k][j] for k in range(size))
                == lengths[j]
                for i in range(size)
                for j in range(size)
                if i != j
            ):
                yield matrix
            return

        i = order[position]
        for row in domains[i]:
            next_trace = diagonal_trace + row[i]
            if next_trace > 6:
                continue
            if any(
                lengths[i] * row[j] != lengths[j] * chosen[j][i]
                for j in chosen
            ):
                continue
            chosen[i] = row
            yield from search(position + 1, next_trace)
            del chosen[i]

    yield from search(0, 0)


def admissible_color_masks(lengths, matrix):
    size = len(lengths)
    # Q_ii is the degree of the induced graph on component i.  Its degree
    # sum must be even.  This removes the five-component type (which has a
    # 3-vertex component of internal degree one) and every (11,11,11) type
    # (whose diagonal entries are a permutation of 1,2,3).
    if any(lengths[i] * matrix[i][i] % 2 for i in range(size)):
        return
    for mask in range(1 << size):
        color_order = sum(
            lengths[i] for i in range(size) if (mask >> i) & 1
        )
        if color_order % 3 != 0:
            continue
        if any(
            lengths[i] == 5
            and not ((mask >> i) & 1)
            and matrix[i][i] == 2
            for i in range(size)
        ):
            continue
        if all(
            lengths[i] >= 5 and matrix[i][i] >= 2
            for i in range(size)
            if (mask >> i) & 1
        ):
            yield mask


def periodic_common_neighbor_ok(lengths, matrix):
    """Necessary local consequence of the full relation A D = D A.

    The rows of an r-by-s cycle-intertwining block repeat after s source
    steps. Thus vertices separated by ``s mod r`` in component i have all
    q_ij neighbors in component j in common. A nonconsecutive pair may have
    only one common neighbor.
    """
    for i, order in enumerate(lengths):
        for shift in range(2, order - 1):
            forced_common = sum(
                matrix[i][j]
                for j, other_order in enumerate(lengths)
                if j != i and other_order % order == shift
            )
            if forced_common > 1:
                return False
    return True


def main():
    totals = {}
    for component_count in (9, 7, 5, 3):
        surviving = []
        for lengths in partitions(33, component_count):
            if sum(length % 2 == 0 for length in lengths) % 2:
                continue
            for matrix in quotient_matrices(lengths):
                masks = tuple(admissible_color_masks(lengths, matrix))
                if masks and periodic_common_neighbor_ok(lengths, matrix):
                    surviving.append((lengths, matrix, masks))
        totals[component_count] = len(surviving)
        print(f"component count {component_count}: {len(surviving)}")
        for lengths, matrix, masks in surviving:
            print(" ", lengths, matrix, tuple(bin(mask) for mask in masks))

    assert totals == {9: 0, 7: 0, 5: 0, 3: 0}


if __name__ == "__main__":
    main()
