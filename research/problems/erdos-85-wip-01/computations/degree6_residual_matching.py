#!/usr/bin/env python3
"""Exhaust the local matching obstruction in the residual d=6 quotient.

The remaining quotient has component sizes (5, 8, 20) and quotient matrix
[[2,0,4],[0,1,5],[1,2,3]], with the 5-cycle colored N.  The common-neighbor
table forces the five X-indexed matchings on Y to factor the complement of
C8.  For every z in the 20-set, its three internal neighbors' Y-label pairs,
together with the image of its own label pair under the internal Y matching,
must partition Y.  This script checks that no such local data exist.

Expected final line: NO LOCAL MODELS 14136
"""

from itertools import combinations, permutations


VERTICES = range(8)


def is_cycle_edge(a, b):
    return (a - b) % 8 in (1, 7)


COMPLEMENT_EDGES = {
    tuple(sorted(edge))
    for edge in combinations(VERTICES, 2)
    if not is_cycle_edge(*edge)
}


def perfect_matchings(remaining=tuple(VERTICES)):
    if not remaining:
        yield frozenset()
        return
    a = remaining[0]
    for b in remaining[1:]:
        edge = tuple(sorted((a, b)))
        if edge not in COMPLEMENT_EDGES:
            continue
        rest = tuple(x for x in remaining if x not in (a, b))
        for matching in perfect_matchings(rest):
            yield matching | {edge}


MATCHINGS = list(perfect_matchings())


def one_factorizations():
    answers = []

    def search(edges, chosen):
        if not edges:
            normalized = tuple(sorted(tuple(sorted(m)) for m in chosen))
            answers.append(normalized)
            return
        edge = min(edges)
        for matching in MATCHINGS:
            if edge in matching and matching <= edges:
                search(edges - matching, chosen + [matching])

    search(COMPLEMENT_EDGES, [])
    return sorted(set(answers))


FACTORIZATIONS = one_factorizations()

# Fix factor 0 at cyclic position 0 and quotient by reflection.
CYCLIC_ORDERS = [
    (0,) + p for p in permutations(range(1, 5)) if p[0] < p[-1]
]

# The three fixed-point-free involutions on four edges of one matching.
EDGE_PAIRINGS = ((1, 0, 3, 2), (2, 3, 0, 1), (3, 2, 1, 0))


def passes_local_partition_test(factorization, order, internal_matching):
    factors = [factorization[index] for index in order]
    masks = [[sum(1 << v for v in edge) for edge in f] for f in factors]
    involution = {
        a: b
        for a, b in internal_matching
        for a, b in ((a, b), (b, a))
    }
    transported = [
        [(1 << involution[e[0]]) | (1 << involution[e[1]]) for e in f]
        for f in factors
    ]

    # We deliberately forget global consistency of the within-fiber and
    # cross-fiber matchings.  Even under this relaxation, every candidate
    # has some local edge for which no four-pair partition is possible.
    for i in range(5):
        for edge_index in range(4):
            possible = False
            for pairing in EDGE_PAIRINGS:
                for upward in range(4):
                    for downward in range(4):
                        four_pairs = (
                            transported[i][edge_index],
                            masks[i][pairing[edge_index]],
                            masks[(i + 2) % 5][upward],
                            masks[(i - 2) % 5][downward],
                        )
                        # Four two-subsets partition Fin 8 exactly when their
                        # bit masks are disjoint and sum to 2^8-1.
                        disjoint = all(
                            four_pairs[a] & four_pairs[b] == 0
                            for a in range(4) for b in range(a + 1, 4)
                        )
                        if disjoint and sum(four_pairs) == 255:
                            possible = True
            if not possible:
                return False
    return True


def main():
    checked = 0
    for factorization in FACTORIZATIONS:
        for order in CYCLIC_ORDERS:
            for internal_matching in MATCHINGS:
                checked += 1
                if passes_local_partition_test(
                    factorization, order, internal_matching
                ):
                    raise SystemExit(f"LOCAL MODEL after {checked} cases")
    print(f"NO LOCAL MODELS {checked}")


if __name__ == "__main__":
    main()
