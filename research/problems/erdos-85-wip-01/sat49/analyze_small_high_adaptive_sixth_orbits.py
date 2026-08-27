#!/usr/bin/env python3
"""Compute exact root-preserving graph-state orbits of the sixth frontier.

The audit propagates every exact sixth job, retains assignments of the 1176
graph-edge variables, and regards vertices 0, 1, and 2 as three distinct
roots.  Weisfeiler--Lehman hashes only bucket possible matches; every orbit
membership is then certified by an exact attributed-graph isomorphism and an
explicit vertex map.

This proves equivalence of the propagated signed graph states.  It does not
by itself prove that the DIMACS auxiliary-variable encoding has the same
automorphisms, so the report must not be used to delete CNF jobs without an
additional encoding-automorphism or graph-semantic bridge.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter, defaultdict
from pathlib import Path

import networkx as nx

from analyze_small_high_adaptive_sixth_units import (
    build_falsified_occurrences,
    edge_endpoints,
    manifest_jobs,
    propagate,
    read_dimacs,
)


def propagated_graph(
    clauses: list[tuple[int, ...]],
    occurrences: dict[int, list[int]],
    base_units: tuple[int, ...],
    assumptions: list[int],
) -> nx.Graph:
    consistent, assignment = propagate(
        clauses, occurrences, base_units, assumptions
    )
    if not consistent:
        raise ValueError("sixth job has a unit-propagation conflict")
    graph = nx.Graph()
    for vertex in range(49):
        root_color = str(vertex) if vertex < 3 else "ordinary"
        graph.add_node(vertex, root=root_color)
    for variable, value in assignment.items():
        endpoints = edge_endpoints(variable)
        if endpoints is not None:
            graph.add_edge(*endpoints, state="1" if value else "0")
    return graph


def exact_orbits(
    jobs: list[tuple[str, list[int]]],
    clauses: list[tuple[int, ...]],
    occurrences: dict[int, list[int]],
    base_units: tuple[int, ...],
) -> tuple[list[dict], int]:
    buckets: dict[str, list[tuple[str, nx.Graph]]] = defaultdict(list)
    for job_id, assumptions in jobs:
        graph = propagated_graph(
            clauses, occurrences, base_units, assumptions
        )
        fingerprint = nx.weisfeiler_lehman_graph_hash(
            graph, node_attr="root", edge_attr="state", iterations=8
        )
        buckets[fingerprint].append((job_id, graph))

    node_match = nx.algorithms.isomorphism.categorical_node_match(
        "root", None
    )
    edge_match = nx.algorithms.isomorphism.categorical_edge_match(
        "state", None
    )
    orbits: list[list[tuple[str, nx.Graph, dict[int, int]]]] = []
    for bucket in buckets.values():
        representatives: list[
            list[tuple[str, nx.Graph, dict[int, int]]]
        ] = []
        for job_id, graph in bucket:
            for orbit in representatives:
                representative_graph = orbit[0][1]
                matcher = nx.algorithms.isomorphism.GraphMatcher(
                    graph,
                    representative_graph,
                    node_match=node_match,
                    edge_match=edge_match,
                )
                if matcher.is_isomorphic():
                    orbit.append((job_id, graph, dict(matcher.mapping)))
                    break
            else:
                representatives.append(
                    [(job_id, graph, {vertex: vertex for vertex in range(49)})]
                )
        orbits.extend(representatives)

    report_orbits = []
    for orbit_id, orbit in enumerate(orbits):
        representative = orbit[0][0]
        report_orbits.append(
            {
                "orbit": orbit_id,
                "representative": representative,
                "size": len(orbit),
                "members": [
                    {
                        "job": job_id,
                        "vertex_map_to_representative": [
                            mapping[vertex] for vertex in range(49)
                        ],
                    }
                    for job_id, _graph, mapping in orbit
                ],
            }
        )
    return report_orbits, len(buckets)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    manifest = json.loads(args.manifest.read_text())
    if manifest.get("schema") != "erdos85-small-high-adaptive-sixth-jobs-v1":
        raise ValueError(f"unsupported manifest schema: {args.manifest}")
    jobs = manifest_jobs(manifest)
    bases = {
        Path(leaf["base"]) for leaf in manifest.get("leaves", {}).values()
    }
    if len(bases) != 1:
        raise ValueError(f"expected one shared base CNF, found {len(bases)}")
    base = next(iter(bases))
    _variables, clauses = read_dimacs(base)
    occurrences = build_falsified_occurrences(clauses)
    base_units = tuple(clause[0] for clause in clauses if len(clause) == 1)
    orbits, hash_bucket_count = exact_orbits(
        jobs, clauses, occurrences, base_units
    )
    if sum(orbit["size"] for orbit in orbits) != len(jobs):
        raise AssertionError("orbit partition does not cover every job")
    report = {
        "scope": "root-preserving propagated signed graph states",
        "dimacs_auxiliary_automorphism_proved": False,
        "manifest": str(args.manifest.resolve()),
        "base": str(base.resolve()),
        "jobs": len(jobs),
        "wl_hash_buckets": hash_bucket_count,
        "exact_orbits": len(orbits),
        "orbit_size_histogram": dict(
            sorted(Counter(orbit["size"] for orbit in orbits).items())
        ),
        "orbits": orbits,
    }
    rendered = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.output is None:
        print(rendered, end="")
    else:
        args.output.write_text(rendered)
        print(f"WROTE {args.output.resolve()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
