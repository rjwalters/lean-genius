#!/usr/bin/env python3
"""Verify the rational three-color action of A=D union S on a Stage-1 WIT."""

from itertools import combinations

from hlift_witness import validate_witness
from test_symbolic_hlift_service import WIT

COMPS = range(4)
ORPHANS = [(omit, copy) for omit in COMPS for copy in range(4)]
OIDX = {orphan: index for index, orphan in enumerate(ORPHANS)}
N = 192


def vid(orphan, x):
    return 12 * OIDX[orphan] + x % 12


def graphs(witness):
    defect = {frozenset((vid(orphan, x), vid(orphan, x + 1)))
              for orphan in ORPHANS for x in range(12)}
    service = set()
    for left, right in combinations(ORPHANS, 2):
        shared = set(witness[left]) & set(witness[right])
        for component in shared:
            delta = (witness[left][component] -
                     witness[right][component]) % 12
            for x in range(12):
                pair = frozenset((vid(left, x), vid(right, x + delta)))
                if pair in service:
                    raise ValueError(f"duplicate service pair {pair}")
                service.add(pair)
    return defect | service


def verify_color_action(witness):
    validate_witness(witness)
    adjacency = graphs(witness)
    neighbors = [set() for _ in range(N)]
    for pair in adjacency:
        left, right = tuple(pair)
        neighbors[left].add(right)
        neighbors[right].add(left)
    assert {len(row) for row in neighbors} == {35}

    for component in COMPS:
        linked = [orphan for orphan in ORPHANS if component in witness[orphan]]
        linked_vertices = {vid(orphan, x) for orphan in linked for x in range(12)}
        colors = []
        for residue in range(3):
            colors.append({vid(orphan, x) for orphan in linked for x in range(12)
                           if (x + witness[orphan][component]) % 3 == residue})
        assert [len(color) for color in colors] == [48, 48, 48]
        for residue, color in enumerate(colors):
            for vertex in range(N):
                actual = len(neighbors[vertex] & color)
                expected = (12 * (vertex in color) -
                            3 * (vertex in linked_vertices) + 8)
                if actual != expected:
                    raise ValueError(
                        f"A-color action failure e={component}, r={residue}, "
                        f"v={vertex}: {actual} != {expected}")
    return {"vertices": N, "A_edges": len(adjacency),
            "identity": "A c_r = 12 c_r - 3 L_e + 8 one"}


if __name__ == "__main__":
    print("STAGE1 COLOR ACTION VERIFIED", verify_color_action(WIT))
