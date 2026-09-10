"""Finite coverage arithmetic for the universal H7 a9 endpoint."""
from itertools import combinations


SHAPES = [
    [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (2, 5), (3, 6), (4, 6), (5, 6)],
    [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (3, 6), (4, 5), (5, 6)],
]


def main():
    for index, edges in enumerate(SHAPES):
        edges = set(edges)
        neighbors = [{w for edge in edges if v in edge for w in edge if w != v}
                     for v in range(7)]
        assert sorted(map(len, neighbors)) == [2, 2, 2, 3, 3, 3, 3]
        assert all(len(neighbors[u] & neighbors[v]) <= 1 for u, v in combinations(range(7), 2))
        triangles = [t for t in combinations(range(7), 3)
                     if all(e in edges for e in combinations(t, 2))]
        assert triangles == [[(0, 1, 2)], [(0, 1, 2), (3, 5, 6)]][index]
        allowed = [e for e in combinations(range(7), 2)
                   if not neighbors[e[0]] & neighbors[e[1]]]
        assert len(allowed) == 6
        triangular_pairs = set(allowed) & edges
        assert triangular_pairs == [set(allowed), {(0, 3), (1, 4), (4, 5)}][index]
        lower_bounds = []
        three_edge_sets = set()
        for mask in range(64):
            x = {e for k, e in enumerate(allowed) if mask >> k & 1}
            forced = x & edges
            covered = {v for t in triangles for v in t} | {v for e in forced for v in e}
            lower = len(triangles)+len(forced)+7-len(covered)
            lower_bounds.append(lower)
            assert lower >= [4, 3][index]
            if lower == 3:
                three_edge_sets.add(frozenset(forced))
        assert min(lower_bounds) == [4, 3][index]
        assert lower_bounds[0] == [5, 3][index]
        if index == 0:
            # The four vertices outside the unique triangle induce a claw.
            remaining = set(range(7))-{v for t in triangles for v in t}
            claw_edges = [e for e in edges if set(e) <= remaining]
            assert set(claw_edges) == {(3, 6), (4, 6), (5, 6)}
            assert all(set(e) & set(f) for e, f in combinations(claw_edges, 2))
            assert not three_edge_sets
        else:
            assert three_edge_sets == {frozenset(), frozenset({(1, 4)}), frozenset({(4, 5)})}
        print('PASS shape', 'AB'[index], ': universal coverage minimum', min(lower_bounds),
              '; X=0 minimum', lower_bounds[0])
    print('No residual spectrum assumed; no complete shape/profile exclusion.')


if __name__ == '__main__':
    main()
