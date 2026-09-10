#!/usr/bin/env python3
"""Direct labelled nine-vertex census of the triple-profile secondary graph.

Enumerate every 3/4-edge graph on R=0..7. Attach root 8 to N=0..5.
Use only a matching on N of size 1..3, positive R-degree for T=6,7,
and the direct no-four-cycle predicate. Quotient by all S6 x S2 relabelings.
No normalized production generator is imported by this census.
"""
from collections import Counter
from itertools import combinations, permutations
import json
from pathlib import Path
import time

EDGES = list(combinations(range(8), 2))
INDEX = {edge: i for i, edge in enumerate(EDGES)}


def encode(edges):
    return sum(1 << INDEX[tuple(sorted(edge))] for edge in edges)


def decode(mask):
    return [edge for i, edge in enumerate(EDGES) if (mask >> i) & 1]


def admissible(edges):
    adjacency = [set() for _ in range(9)]
    for u, v in [*edges, *((8, i) for i in range(6))]:
        adjacency[u].add(v); adjacency[v].add(u)
    near = [sum(v < 6 for v in adjacency[u]) for u in range(6)]
    m = sum(near) // 2
    if max(near) > 1 or not 1 <= m <= 3:
        return None
    if not adjacency[6] or not adjacency[7]:
        return None
    # Direct pair-intersection test, not the production incremental edge test.
    if any(len(adjacency[u] & adjacency[v]) > 1 for u, v in combinations(range(9), 2)):
        return None
    return (m, len(edges))


def census():
    started = time.monotonic()
    labelled = {}; visited = 0
    for r in (3, 4):
        for edges in combinations(EDGES, r):
            visited += 1
            branch = admissible(edges)
            if branch is not None:
                labelled[encode(edges)] = branch
    group = [(*p, *q) for p in permutations(range(6)) for q in [(6, 7), (7, 6)]]
    assert len(group) == 1440 and len(set(group)) == 1440
    unseen = set(labelled); orbits = []; assignment = {}
    while unseen:
        representative = min(unseen); edges = decode(representative)
        orbit = {encode((perm[u], perm[v]) for u, v in edges) for perm in group}
        assert orbit <= unseen  # Every image valid; distinct orbits cannot overlap.
        branch = labelled[representative]
        assert {labelled[image] for image in orbit} == {branch}
        for image in orbit:
            assignment[image] = representative
        unseen.difference_update(orbit)
        orbits.append({'representative': representative, 'edges': edges,
                       'm': branch[0], 'r': branch[1], 'orbit_size': len(orbit)})
    assert set(assignment) == set(labelled)
    result = {'scope': 'Secondary R normal-form coverage only; no full graph exclusion or Lean proof',
              'graphs_examined': visited, 'labelled_survivors': len(labelled),
              'group_order': len(group), 'orbits': orbits,
              'labelled_by_branch': {str(k): v for k,v in sorted(Counter(labelled.values()).items())},
              'orbits_by_branch': {str(k): v for k,v in sorted(Counter((o['m'],o['r']) for o in orbits).items())},
              'elapsed_seconds': time.monotonic()-started}
    return result, assignment


if __name__ == '__main__':
    import argparse
    parser=argparse.ArgumentParser();parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args();result,_=census()
    with args.output.open('x') as out:json.dump(result,out,indent=2);out.write('\n')
    print(json.dumps({k:v for k,v in result.items() if k!='orbits'}))
