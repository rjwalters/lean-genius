#!/usr/bin/env python3
"""Exhaust the order-six Latin obstruction behind the all-triangle cell.

A reduced Latin square has first row and first column 0,1,...,5.  Its six
columns are permutations.  Two columns form a triangle-bearing bipartite
two-factor precisely when their relative permutation has cycle type (3,3).
This program checks whether the six columns admit a perfect matching of three
such pairs.

The classical count of reduced Latin squares of order six is 9,408.  We assert
that count as a completeness guard and then assert that no qualifying square
exists.  This is a discovery/reproducibility artifact; the final proof still
requires a kernel-checked Lean replay.
"""

N = 6


def relative_type_three_three(p: list[int], q: list[int]) -> bool:
    inverse_p = [0] * N
    for x, y in enumerate(p):
        inverse_p[y] = x
    relative = [inverse_p[q[x]] for x in range(N)]
    seen: set[int] = set()
    lengths: list[int] = []
    for x in range(N):
        if x in seen:
            continue
        y = x
        length = 0
        while y not in seen:
            seen.add(y)
            length += 1
            y = relative[y]
        lengths.append(length)
    return sorted(lengths) == [3, 3]


def triangle_pairing(columns: list[list[int]]) -> list[tuple[int, int]] | None:
    adjacent = [
        [relative_type_three_three(columns[i], columns[j]) for j in range(N)]
        for i in range(N)
    ]

    def extend(remaining: list[int], pairs: list[tuple[int, int]]):
        if not remaining:
            return pairs
        i = remaining[0]
        for j in remaining[1:]:
            if adjacent[i][j]:
                result = extend(
                    [x for x in remaining if x != i and x != j],
                    pairs + [(i, j)],
                )
                if result is not None:
                    return result
        return None

    return extend(list(range(N)), [])


def enumerate_reduced() -> tuple[int, list[tuple[list[list[int]], list[tuple[int, int]]]]]:
    rows = [list(range(N))]
    column_used = [{j} for j in range(N)]
    count = 0
    witnesses = []

    def search(row_index: int) -> None:
        nonlocal count
        if row_index == N:
            count += 1
            columns = [[rows[x][i] for x in range(N)] for i in range(N)]
            pairing = triangle_pairing(columns)
            if pairing is not None:
                witnesses.append(([row[:] for row in rows], pairing))
            return

        row = [0] * N

        def fill(position: int, used: set[int]) -> None:
            if position == N:
                rows.append(row[:])
                search(row_index + 1)
                rows.pop()
                return
            candidates = [row_index] if position == 0 else range(N)
            for value in candidates:
                if value in used or value in column_used[position]:
                    continue
                row[position] = value
                used.add(value)
                column_used[position].add(value)
                fill(position + 1, used)
                column_used[position].remove(value)
                used.remove(value)

        fill(0, set())

    search(1)
    return count, witnesses


if __name__ == "__main__":
    reduced_count, found = enumerate_reduced()
    print(f"reduced Latin squares: {reduced_count}")
    print(f"three-(3,3)-factor witnesses: {len(found)}")
    assert reduced_count == 9_408
    assert not found
