#!/usr/bin/env python3
"""Count disjoint K two-factors modulo the symmetries of a fixed C16.

Normalize the H-factor by H(x,y) iff y=x or y=x+1 modulo 8.  Every
bipartite two-factor K is the union of two perfect matchings.  We enumerate
all matching pairs which avoid H, deduplicate the resulting K edge sets, and
then quotient by the shore-preserving dihedral automorphism group of H.

This measures whether a per-K certificate family can be small using only the
obvious C16 symmetry.  It cannot: the quotient still has 117,737 members.
"""

from itertools import permutations

N = 8


def eligible_matchings():
    return [
        p
        for p in permutations(range(N))
        if all(p[x] not in (x, (x + 1) % N) for x in range(N))
    ]


def two_factors(matchings):
    graphs = set()
    for index, p in enumerate(matchings):
        for q in matchings[index + 1 :]:
            if all(a != b for a, b in zip(p, q)):
                graphs.add(tuple((1 << a) | (1 << b) for a, b in zip(p, q)))
    return graphs


def dihedral_maps():
    maps = []
    for offset in range(N):
        for reflected in (False, True):
            row_map = [
                (-x + offset) % N if reflected else (x + offset) % N
                for x in range(N)
            ]
            mask_map = []
            for mask in range(1 << N):
                image = 0
                for y in range(N):
                    if mask >> y & 1:
                        target = (
                            (-y + offset + 1) % N
                            if reflected
                            else (y + offset) % N
                        )
                        image |= 1 << target
                mask_map.append(image)
            maps.append((row_map, mask_map))
    return maps


def canonical(graph, maps):
    best = graph
    for row_map, mask_map in maps:
        image = [0] * N
        for x, mask in enumerate(graph):
            image[row_map[x]] = mask_map[mask]
        best = min(best, tuple(image))
    return best


if __name__ == "__main__":
    matchings = eligible_matchings()
    graphs = two_factors(matchings)
    graph_count = len(graphs)
    maps = dihedral_maps()
    orbits = set()
    while graphs:
        orbits.add(canonical(graphs.pop(), maps))

    print(f"eligible perfect matchings: {len(matchings)}")
    print(f"disjoint K two-factors: {graph_count}")
    print(f"shore-preserving D16 orbits: {len(orbits)}")
    assert len(matchings) == 4_738
    assert graph_count == 1_867_363
    assert len(orbits) == 117_737
