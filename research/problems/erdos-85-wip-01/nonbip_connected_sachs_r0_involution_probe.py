#!/usr/bin/env python3
"""Falsify the one-centre local Sachs splice on the exact q=4 control.

Divergence round #47 proposed pairing spanning Sachs subgraphs at the first
zero-D-codegree pair x,y in distinct elementary components, using their unique
common A-neighbour c.  Such a local involution needs a different elementary
cover on the union of the components containing x,y,c.

The banked q=4 fixed-free control has a perfect matching for which the first
R0 pair is (0,3), its unique centre is 2, and the relevant two matching
components cover {0,1,2,3}.  The induced A-graph on these four vertices has
only the original elementary cover {(0,1),(2,3)}.  Hence no splice supported
on those components exists.  A surviving Sachs involution must be genuinely
nonlocal (and must specify how its enlarged support is chosen reversibly).
"""

from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path


HERE = Path(__file__).resolve().parent
CONTROL = HERE / "binary_q4_fixed_free_disconnected_control.py"
SPEC = spec_from_file_location("q4_control", CONTROL)
assert SPEC is not None and SPEC.loader is not None
CONTROL_MODULE = module_from_spec(SPEC)
SPEC.loader.exec_module(CONTROL_MODULE)

N = CONTROL_MODULE.N
A = CONTROL_MODULE.adjacency(CONTROL_MODULE.A_EDGES)


def is_elementary_cover(vertices: set[int], edges: set[tuple[int, int]]) -> bool:
    """Every component is one edge or a simple cycle, and all vertices occur."""
    neighbors = {x: set() for x in vertices}
    for x, y in edges:
        if x not in vertices or y not in vertices or y not in A[x]:
            return False
        neighbors[x].add(y)
        neighbors[y].add(x)
    if any(len(neighbors[x]) not in (1, 2) for x in vertices):
        return False
    unseen = set(vertices)
    while unseen:
        root = min(unseen)
        component = {root}
        stack = [root]
        while stack:
            x = stack.pop()
            for y in neighbors[x] - component:
                component.add(y)
                stack.append(y)
        unseen -= component
        degrees = [len(neighbors[x]) for x in component]
        if len(component) == 2:
            if degrees != [1, 1]:
                return False
        elif len(component) < 3 or any(degree != 2 for degree in degrees):
            return False
    return True


def elementary_covers(vertices: set[int]) -> list[frozenset[tuple[int, int]]]:
    induced_edges = sorted(
        (x, y) for x in vertices for y in A[x] if x < y and y in vertices
    )
    covers = []
    for mask in range(1 << len(induced_edges)):
        edges = {
            edge for index, edge in enumerate(induced_edges) if (mask >> index) & 1
        }
        if is_elementary_cover(vertices, edges):
            covers.append(frozenset(edges))
    return covers


def main() -> None:
    matching = frozenset(
        {
            (0, 1), (2, 3), (4, 10), (5, 8),
            (6, 9), (7, 15), (11, 12), (13, 14),
        }
    )
    assert is_elementary_cover(set(range(N)), set(matching))

    common_a = A[0] & A[3]
    assert common_a == {2}

    common_count = {
        (x, y): len(A[x] & A[y])
        for x in range(N)
        for y in range(x + 1, N)
    }
    defect_edges = {pair for pair, count in common_count.items() if count == 0}
    D = CONTROL_MODULE.adjacency(defect_edges)
    assert 3 not in D[0]
    assert not (D[0] & D[3])

    local_vertices = {0, 1, 2, 3}
    local_cover = frozenset({(0, 1), (2, 3)})
    covers = elementary_covers(local_vertices)
    assert covers == [local_cover]

    print("verified q=4 obstruction to the local R0-centred Sachs splice")
    print("R0 pair=(0,3), unique A-centre=2, local support={0,1,2,3}")
    print("the induced support has exactly one elementary cover: (01)(23)")


if __name__ == "__main__":
    main()
