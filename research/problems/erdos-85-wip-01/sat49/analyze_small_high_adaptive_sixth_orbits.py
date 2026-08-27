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


SelectorTuple = tuple[int, int, int, int, int, int, int]


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
) -> tuple[list[dict], int, dict[str, nx.Graph]]:
    buckets: dict[str, list[tuple[str, nx.Graph]]] = defaultdict(list)
    graphs = {}
    for job_id, assumptions in jobs:
        graph = propagated_graph(
            clauses, occurrences, base_units, assumptions
        )
        fingerprint = nx.weisfeiler_lehman_graph_hash(
            graph, node_attr="root", edge_attr="state", iterations=8
        )
        graphs[job_id] = graph
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
    return report_orbits, len(buckets), graphs


def compose_permutations(
    left: tuple[int, ...], right: tuple[int, ...]
) -> tuple[int, ...]:
    return tuple(left[right[value]] for value in range(8))


def selector_value_group() -> list[tuple[int, ...]]:
    """The eight matching-pair/block permutations on indices 4 through 7."""
    identity = tuple(range(8))
    generators = [
        (0, 1, 2, 3, 5, 4, 6, 7),
        (0, 1, 2, 3, 4, 5, 7, 6),
        (0, 1, 2, 3, 6, 7, 4, 5),
    ]
    group = {identity}
    frontier = [identity]
    while frontier:
        permutation = frontier.pop()
        for generator in generators:
            composite = compose_permutations(generator, permutation)
            if composite not in group:
                group.add(composite)
                frontier.append(composite)
    if len(group) != 8:
        raise AssertionError(f"unexpected selector group order: {len(group)}")
    return sorted(group)


def transform_selector_tuple(
    selectors: SelectorTuple,
    permutation: tuple[int, ...],
    swap_sixth: bool,
) -> SelectorTuple:
    li, ri, ai, bi, ci, di, ei = selectors
    old_coordinates = (ri, ai, bi, ci)
    new_coordinates = [0, 0, 0, 0]
    for source, value in enumerate(old_coordinates):
        destination = permutation[4 + source] - 4
        new_coordinates[destination] = permutation[value]
    new_di, new_ei = permutation[di], permutation[ei]
    if swap_sixth:
        new_di, new_ei = new_ei, new_di
    return (
        permutation[li],
        *new_coordinates,
        new_di,
        new_ei,
    )


def selector_tuples(manifest: dict) -> dict[str, SelectorTuple]:
    result = {}
    for leaf in manifest.get("leaves", {}).values():
        prefix = (
            int(leaf["third_left_index"]),
            int(leaf["third_right_index"]),
            int(leaf["fourth_left_index"]),
            int(leaf["fourth_right_index"]),
            int(leaf["fifth_selector_index"]),
        )
        for job in leaf.get("jobs", []):
            result[str(job["id"])] = (
                *prefix,
                int(job["left_selector_index"]),
                int(job["right_selector_index"]),
            )
    return result


def vertex_map(
    permutation: tuple[int, ...], swap_sixth: bool
) -> dict[int, int]:
    mapping = {vertex: vertex for vertex in range(49)}
    for index in range(4, 8):
        mapping[14 + index - 4] = 14 + permutation[index] - 4
        mapping[20 + index - 4] = 20 + permutation[index] - 4
    if swap_sixth:
        mapping[24], mapping[25] = 25, 24
    return mapping


def selector_group_orbits(
    manifest: dict,
    graphs: dict[str, nx.Graph],
) -> list[dict]:
    """Verify the credible 16-map selector subgroup and return its orbits."""
    tuples_by_job = selector_tuples(manifest)
    jobs_by_tuple = {value: job for job, value in tuples_by_job.items()}
    if len(jobs_by_tuple) != len(tuples_by_job):
        raise ValueError("selector tuples do not uniquely identify sixth jobs")
    transformations = [
        (permutation, swap_sixth)
        for permutation in selector_value_group()
        for swap_sixth in (False, True)
    ]
    unseen = set(tuples_by_job)
    orbits = []
    while unseen:
        representative = min(unseen)
        representative_tuple = tuples_by_job[representative]
        members = []
        for permutation, swap_sixth in transformations:
            transformed = transform_selector_tuple(
                representative_tuple, permutation, swap_sixth
            )
            target = jobs_by_tuple.get(transformed)
            if target is None:
                raise AssertionError(
                    f"selector transformation leaves the frontier: {transformed}"
                )
            mapping = vertex_map(permutation, swap_sixth)
            relabeled = nx.relabel_nodes(graphs[representative], mapping)
            if not nx.utils.graphs_equal(relabeled, graphs[target]):
                raise AssertionError(
                    f"vertex map does not preserve signed state: {target}"
                )
            members.append(
                {
                    "job": target,
                    "selector_tuple": list(transformed),
                    "vertex_map_from_representative": [
                        mapping[vertex] for vertex in range(49)
                    ],
                }
            )
        member_jobs = {member["job"] for member in members}
        if len(member_jobs) != len(transformations):
            raise AssertionError("selector group action has a nontrivial stabilizer")
        unseen.difference_update(member_jobs)
        orbits.append(
            {
                "representative": representative,
                "size": len(member_jobs),
                "members": sorted(members, key=lambda member: member["job"]),
            }
        )
    return orbits


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
    orbits, hash_bucket_count, graphs = exact_orbits(
        jobs, clauses, occurrences, base_units
    )
    if sum(orbit["size"] for orbit in orbits) != len(jobs):
        raise AssertionError("orbit partition does not cover every job")
    selector_orbits = selector_group_orbits(manifest, graphs)
    if sum(orbit["size"] for orbit in selector_orbits) != len(jobs):
        raise AssertionError("selector-group orbits do not cover every job")
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
        "selector_group_order": 16,
        "selector_group_signed_state_maps_verified": True,
        "selector_group_dimacs_automorphism_proved": False,
        "selector_group_orbit_count": len(selector_orbits),
        "selector_group_orbit_size_histogram": dict(
            sorted(Counter(orbit["size"] for orbit in selector_orbits).items())
        ),
        "selector_group_orbits": selector_orbits,
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
