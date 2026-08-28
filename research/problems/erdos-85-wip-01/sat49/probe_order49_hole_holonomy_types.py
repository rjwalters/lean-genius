#!/usr/bin/env python3
"""Classify the three pairwise five-hole matchings up to part-preserving isomorphism."""

from __future__ import annotations

import argparse
from collections import Counter

import networkx as nx
import numpy as np
import z3
from scipy.optimize import linprog

from extract_order49_two_color_farkas import primal_matrices
from probe_order49_hole_endpoint_cover import holes
from probe_order49_three_open_code_holonomy import (
    CODES, PAIR01, PAIR02, PAIR12, build_solver, support,
)


def hole_graph(owner: list[list[int]]) -> nx.Graph:
    graph = nx.Graph()
    for h in range(3):
        for u in CODES[h]:
            if support(u) == 1:
                graph.add_node((h, u), part=h)
    for h, k in ((0, 1), (0, 2), (1, 2)):
        for u, v in holes(owner, (h, k)):
            graph.add_edge((h, u), (k, v))
    return graph


def component_signature(graph: nx.Graph) -> tuple:
    components = []
    for vertices in nx.connected_components(graph):
        subgraph = graph.subgraph(vertices)
        part_degree = tuple(sorted(
            (graph.nodes[v]["part"], subgraph.degree(v)) for v in vertices
        ))
        components.append((len(vertices), subgraph.number_of_edges(), part_degree))
    return tuple(sorted(components))


def classify(graph: nx.Graph, representatives: list[nx.Graph]) -> int:
    node_match = nx.algorithms.isomorphism.categorical_node_match("part", None)
    for index, representative in enumerate(representatives):
        if nx.is_isomorphic(graph, representative, node_match=node_match):
            return index
    representatives.append(graph.copy())
    return len(representatives) - 1


def sparse_dual_shape(owner: list[list[int]]) -> tuple:
    aeq, beq, aub, bub, _pairs, _eq_names, _ub_names = primal_matrices(owner, {0, 1})
    m_eq, n = aeq.shape
    m_ub = aub.shape[0]
    coefficients = np.concatenate((aeq.T, -aeq.T, aub.T), axis=1)
    rhs = np.concatenate((beq, -beq, bub))
    result = linprog(
        np.ones(coefficients.shape[1]),
        A_ub=-coefficients, b_ub=np.zeros(n),
        A_eq=rhs[None, :], b_eq=np.asarray([-1.0]),
        bounds=(0, None), method="highs",
    )
    if not result.success:
        return ("failed",)
    y = result.x[:m_eq] - result.x[m_eq:2 * m_eq]
    lam = result.x[2 * m_eq:]
    rationalized = lambda values: tuple(sorted(round(float(value), 6) for value in values if value > 1e-8))
    return (
        rationalized(-y),
        rationalized(lam),
        int(np.sum(coefficients @ result.x > 1e-8)),
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--samples", type=int, default=128)
    parser.add_argument("--profile", choices=("000", "001"), required=True)
    parser.add_argument("--dual", action="store_true")
    args = parser.parse_args()

    solver, variables = build_solver()
    matching_edges = (
        variables[0][PAIR01] == PAIR02,
        variables[1][PAIR01] == PAIR12,
        variables[2][PAIR02] == PAIR12,
    )
    if args.profile == "000":
        solver.add(*(z3.Not(edge) for edge in matching_edges))
    else:
        solver.add(z3.Not(matching_edges[0]), matching_edges[1], z3.Not(matching_edges[2]))

    representatives: list[nx.Graph] = []
    counts = Counter()
    signatures = {}
    dual_shapes = Counter()
    for sample in range(args.samples):
        if solver.check() != z3.sat:
            break
        model = solver.model()
        owner = [
            [model.eval(variables[h][v]).as_long() for v in range(46)]
            for h in range(3)
        ]
        graph = hole_graph(owner)
        kind = classify(graph, representatives)
        counts[kind] += 1
        signatures[kind] = component_signature(graph)
        if args.dual:
            dual_shapes[(kind, sparse_dual_shape(owner))] += 1
        solver.add(z3.Or(*(
            variables[h][v] != owner[h][v]
            for h in range(3) for v in range(46)
        )))
    print(f"profile={args.profile} sampled={sum(counts.values())} types={len(representatives)}")
    for kind in sorted(counts):
        print(f"type={kind} count={counts[kind]} signature={signatures[kind]}")
        if args.dual:
            for (dual_kind, shape), count in sorted(dual_shapes.items(), key=str):
                if dual_kind == kind:
                    print(f"  dual_count={count} shape={shape}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
