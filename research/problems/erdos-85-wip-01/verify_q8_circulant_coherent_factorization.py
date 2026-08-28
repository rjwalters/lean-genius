#!/usr/bin/env python3
"""Exhaust the q=8 circulant coherent-factorization ansatz.

An entry A[c,d] is a two-subset of Z/16.  Reciprocity is
A[d,c] = -A[c,d], diagonal entries are {s,-s}, and for every c != d
the four difference rectangles A[c,e]-A[d,e] must partition Z/16.

The search is dependency-free.  On the reference machine it takes about
seven minutes and visits 766168 backtracking nodes.
"""

from itertools import combinations

N = 16
R = 4
SUBSETS = [(a, b) for a in range(N) for b in range(a + 1, N)]
DIAGONALS = [(a, N - a) for a in range(1, N // 2)]
EDGES = list(combinations(range(R), 2))


def negate(a):
    return tuple((-x) % N for x in a)


def entry(values, i, j):
    a = values[min(i, j), max(i, j)]
    return a if i <= j else negate(a)


def rectangle(a, b):
    return [(x - y) % N for x in a for y in b]


def partial_pair_is_binary(values, c, d):
    """All currently determined rectangles for (c,d) are disjoint 4-sets."""
    seen = set()
    for e in range(R):
        ce = min(c, e), max(c, e)
        de = min(d, e), max(d, e)
        if ce not in values or de not in values:
            continue
        block = rectangle(entry(values, c, e), entry(values, d, e))
        if len(set(block)) != 4 or seen.intersection(block):
            return False
        seen.update(block)
    return True


def q4_calibration():
    """The two-color Z/8 version is satisfiable (and hence no fake base no-go)."""
    n = 8
    subsets = list(combinations(range(n), 2))
    diagonals = sorted({tuple(sorted((s, (-s) % n))) for s in range(n)
                        if s != (-s) % n})
    count = 0
    for d0 in diagonals:
        for d1 in diagonals:
            for a in subsets:
                a10 = tuple((-x) % n for x in a)
                differences = [(x - y) % n for x in d0 for y in a10]
                differences += [(x - y) % n for x in a for y in d1]
                count += sorted(differences) == list(range(n))
    assert count == 32
    return count


def q8_exhaustion():
    nodes = 0
    spectra = 0

    # Equal diagonal two-sets make the endpoint rectangles for that color pair
    # collide.  Thus all four diagonal types are distinct.  Color relabeling
    # lets us enumerate their 35 increasing choices.
    for diagonal_indices in combinations(range(len(DIAGONALS)), R):
        spectra += 1
        values = {(i, i): DIAGONALS[diagonal_indices[i]] for i in range(R)}
        domains = {}

        # Endpoint pruning: for edge cd, the e=c and e=d rectangles already
        # contribute eight distinct residues in every possible completion.
        for c, d in EDGES:
            candidates = []
            for a in SUBSETS:
                values[c, d] = a
                if partial_pair_is_binary(values, c, d):
                    candidates.append(a)
            del values[c, d]
            assert candidates
            domains[c, d] = candidates

        def search(unassigned):
            nonlocal nodes
            if not unassigned:
                return dict(values)

            # Exact MRV after testing every candidate against every pair whose
            # next rectangle it determines.  This is only pruning, not an
            # additional mathematical assumption.
            best_edge = None
            best_candidates = None
            for edge in unassigned:
                surviving = []
                for a in domains[edge]:
                    values[edge] = a
                    if all(partial_pair_is_binary(values, c, d) for c, d in EDGES):
                        surviving.append(a)
                del values[edge]
                if not surviving:
                    return None
                if best_candidates is None or len(surviving) < len(best_candidates):
                    best_edge = edge
                    best_candidates = surviving

            remaining = [edge for edge in unassigned if edge != best_edge]
            for a in best_candidates:
                nodes += 1
                values[best_edge] = a
                witness = search(remaining)
                if witness is not None:
                    return witness
            del values[best_edge]
            return None

        witness = search(EDGES)
        assert witness is None, (diagonal_indices, witness)

    assert spectra == 35
    assert nodes == 766168
    return spectra, nodes


if __name__ == "__main__":
    print("q4 raw solutions:", q4_calibration())
    spectra, nodes = q8_exhaustion()
    print("q8: UNSAT")
    print("diagonal spectra:", spectra)
    print("backtracking nodes:", nodes)
