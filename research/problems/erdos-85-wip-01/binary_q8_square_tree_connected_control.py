#!/usr/bin/env python3
"""Coarse q=8 control for the defect cofactor-square invariant.

This graph is *not* asserted to admit the required symmetric binary incidence
square root.  Its purpose is to show that order, degree, nonbipartiteness, high
connectivity, and square spanning-tree count do not by themselves contradict
the NONBIP-CONNECTED defect profile.
"""

from math import isqrt

import networkx as nx
import sympy as sp


Q = 8
N = Q * Q
POSITIVE_DIFFERENCES = (9, 16, 26, 32)
EXPECTED_TREE_COUNT = 48752669171724046437889868931025994266176213182016


def circulant_control() -> nx.Graph:
    graph = nx.Graph()
    graph.add_nodes_from(range(N))
    for x in range(N):
        for delta in POSITIVE_DIFFERENCES:
            graph.add_edge(x, (x + delta) % N)
            graph.add_edge(x, (x - delta) % N)
    return graph


def spanning_tree_count(graph: nx.Graph) -> int:
    laplacian = nx.laplacian_matrix(graph).toarray().tolist()
    principal_cofactor = [row[:-1] for row in laplacian[:-1]]
    return int(sp.Matrix(principal_cofactor).det())


def main() -> None:
    graph = circulant_control()
    assert graph.number_of_nodes() == N
    assert set(dict(graph.degree()).values()) == {Q - 1}
    assert nx.is_connected(graph)
    assert not nx.is_bipartite(graph)
    assert nx.node_connectivity(graph) == Q - 1

    tree_count = spanning_tree_count(graph)
    root = isqrt(tree_count)
    assert tree_count == EXPECTED_TREE_COUNT
    assert root * root == tree_count

    print(f"vertices={N}")
    print(f"degree={Q - 1}")
    print(f"vertex_connectivity={nx.node_connectivity(graph)}")
    print(f"spanning_trees={tree_count}={root}^2")


if __name__ == "__main__":
    main()
