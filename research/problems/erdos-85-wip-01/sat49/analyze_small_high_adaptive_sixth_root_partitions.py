#!/usr/bin/env python3
"""Probe the three saturated-root coordinate partitions on sixth reps.

This is a graph-semantic relaxation, not a SAT solver launch.  Each degree-8
root has eight fixed neighbours.  C4-freeness makes those neighbours the
centres of a balanced partition of the other 48 vertices into fibres of size
six.  Pairwise coordinate projections are injective away from the shared-centre
cell.  The script asks Z3 for such triples, extracts each missing 7-point
perfect matching, and reports the cycle type of their triangle holonomy.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
from collections import Counter
from pathlib import Path

import networkx as nx

from analyze_small_high_adaptive_sixth_orbits import propagated_graph
from analyze_small_high_adaptive_sixth_units import (
    build_falsified_occurrences,
    manifest_jobs,
    read_dimacs,
)


def edge(u: int, v: int) -> tuple[int, int]:
    return (u, v) if u < v else (v, u)


def canonical_job_ids(orbit_report: dict) -> list[str]:
    return [orbit["representative"] for orbit in orbit_report["selector_group_orbits"]]


def coordinate_smt(graph: nx.Graph) -> tuple[str, list[str]]:
    positive = {
        edge(u, v)
        for u, v, data in graph.edges(data=True)
        if data["state"] == "1"
    }
    negative = {
        edge(u, v)
        for u, v, data in graph.edges(data=True)
        if data["state"] == "0"
    }
    root_neighbours = [
        [w for w in range(49) if w != root and edge(root, w) in positive]
        for root in range(3)
    ]
    if [len(row) for row in root_neighbours] != [8, 8, 8]:
        raise AssertionError("the three high-root neighbourhoods are not saturated")

    variables = [f"c_{root}_{x}" for root in range(3) for x in range(49) if x != root]
    lines = ["(set-logic QF_LIA)"]
    lines.extend(f"(declare-const {variable} Int)" for variable in variables)
    for root in range(3):
        for x in range(49):
            if x == root:
                continue
            candidates = [
                centre
                for centre in root_neighbours[root]
                if centre != x and edge(x, centre) not in negative
            ]
            lines.append(
                "(assert (or "
                + " ".join(f"(= c_{root}_{x} {centre})" for centre in candidates)
                + "))"
            )
            forced = [centre for centre in candidates if edge(x, centre) in positive]
            if forced:
                if len(forced) != 1:
                    raise AssertionError("a root coordinate is multiply forced")
                lines.append(f"(assert (= c_{root}_{x} {forced[0]}))")
        for centre in root_neighbours[root]:
            terms = [
                f"(ite (= c_{root}_{x} {centre}) 1 0)"
                for x in range(49)
                if x != root
            ]
            lines.append(f"(assert (= (+ {' '.join(terms)}) 6))")

    for left in range(3):
        for right in range(left + 1, 3):
            shared = set(root_neighbours[left]) & set(root_neighbours[right])
            if len(shared) != 1:
                raise AssertionError("each pair of root neighbourhoods must meet once")
            shared_centre = next(iter(shared))
            for x in range(49):
                if x in (left, right):
                    continue
                # Both coordinates name the same graph edge x--shared_centre.
                lines.append(
                    f"(assert (= (= c_{left}_{x} {shared_centre}) "
                    f"(= c_{right}_{x} {shared_centre})))"
                )
            for x in range(49):
                if x in (left, right):
                    continue
                for y in range(x + 1, 49):
                    if y in (left, right):
                        continue
                    # If two records repeat both coordinates, their two
                    # centres must coincide, so they give only one common
                    # neighbour rather than a C4.
                    lines.append(
                        "(assert (or "
                        f"(not (= c_{left}_{x} c_{left}_{y})) "
                        f"(not (= c_{right}_{x} c_{right}_{y})) "
                        f"(= c_{left}_{x} c_{right}_{x})))"
                    )
    lines.append("(check-sat)")
    lines.append("(get-value (" + " ".join(variables) + "))")
    return "\n".join(lines) + "\n", variables


def solve_coordinates(
    graph: nx.Graph, timeout: int, seed: int
) -> dict[tuple[int, int], int] | None:
    smt, variables = coordinate_smt(graph)
    smt = f"(set-option :random-seed {seed})\n(set-option :smt.random_seed {seed})\n" + smt
    completed = subprocess.run(
        ["z3", "-in", f"-T:{timeout}"],
        input=smt,
        text=True,
        capture_output=True,
        check=False,
    )
    if completed.stdout.startswith("unsat"):
        return None
    if not completed.stdout.startswith("sat"):
        raise RuntimeError(completed.stdout.strip() or completed.stderr.strip())
    values = {
        (int(root), int(vertex)): int(value)
        for root, vertex, value in re.findall(
            r"\(c_(\d+)_(\d+)\s+(\d+)\)", completed.stdout
        )
    }
    if len(values) != len(variables):
        raise AssertionError(f"parsed {len(values)} of {len(variables)} coordinates")
    return values


def complement_matching(
    values: dict[tuple[int, int], int], left: int, right: int
) -> tuple[int, ...]:
    left_symbols = sorted({values[left, x] for x in range(49) if x != left})
    right_symbols = sorted({values[right, x] for x in range(49) if x != right})
    used = {
        (values[left, x], values[right, x])
        for x in range(49)
        if x not in (left, right)
    }
    # Fuse the two omitted roots into the unique shared-centre record.
    used.add((values[left, right], values[right, left]))
    shared = set(left_symbols) & set(right_symbols)
    if len(shared) != 1:
        raise AssertionError("root symbol sets do not have one shared centre")
    shared_centre = next(iter(shared))
    diagonal_multiplicity = sum(
        values[left, x] == shared_centre and values[right, x] == shared_centre
        for x in range(49)
        if x not in (left, right)
    ) + 1
    if diagonal_multiplicity != 6 or len(used) != 43:
        raise AssertionError(
            f"unexpected shared cell: multiplicity={diagonal_multiplicity}, distinct={len(used)}"
        )
    left_other = [symbol for symbol in left_symbols if symbol != shared_centre]
    right_other = [symbol for symbol in right_symbols if symbol != shared_centre]
    missing = sorted(
        (a, b) for a in left_other for b in right_other if (a, b) not in used
    )
    if len(missing) != 7:
        raise AssertionError(f"expected seven nonshared missing cells, found {len(missing)}")
    if Counter(a for a, _ in missing) != Counter(left_other):
        raise AssertionError("missing cells do not cover each left symbol once")
    if Counter(b for _, b in missing) != Counter(right_other):
        raise AssertionError("missing cells do not cover each right symbol once")
    return tuple(100 * a + b for a, b in missing)


def matching_map(matching: tuple[int, ...], shared: int) -> dict[int, int]:
    result = {encoded // 100: encoded % 100 for encoded in matching}
    result[shared] = shared
    return result


def holonomy_cycle_type(
    matchings: tuple[tuple[int, ...], tuple[int, ...], tuple[int, ...]]
) -> tuple[int, ...]:
    ab = matching_map(matchings[0], 3)
    ac = matching_map(matchings[1], 4)
    bc = matching_map(matchings[2], 5)
    ac_inverse = {value: key for key, value in ac.items()}
    permutation = {a: ac_inverse[bc[ab[a]]] for a in ab}
    unseen = set(permutation)
    cycles = []
    while unseen:
        start = min(unseen)
        x = start
        length = 0
        while x in unseen:
            unseen.remove(x)
            x = permutation[x]
            length += 1
        if x != start:
            raise AssertionError("triangle holonomy is not a permutation")
        cycles.append(length)
    return tuple(sorted(cycles))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--orbits", type=Path, required=True)
    parser.add_argument("--limit", type=int)
    parser.add_argument("--timeout", type=int, default=30)
    parser.add_argument("--seeds", type=int, default=1)
    parser.add_argument("--quiet", action="store_true")
    args = parser.parse_args()

    manifest = json.loads(args.manifest.read_text())
    orbit_report = json.loads(args.orbits.read_text())
    jobs = dict(manifest_jobs(manifest))
    job_ids = canonical_job_ids(orbit_report)
    if args.limit is not None:
        job_ids = job_ids[: args.limit]
    bases = {Path(leaf["base"]) for leaf in manifest["leaves"].values()}
    if len(bases) != 1:
        raise ValueError("expected one shared base CNF")
    _variables, clauses = read_dimacs(next(iter(bases)))
    occurrences = build_falsified_occurrences(clauses)
    base_units = tuple(clause[0] for clause in clauses if len(clause) == 1)

    histogram: Counter[tuple[int, ...]] = Counter()
    unsat = []
    for job_id in job_ids:
        graph = propagated_graph(
            clauses, occurrences, base_units, jobs[job_id]
        )
        for seed in range(args.seeds):
            values = solve_coordinates(graph, args.timeout, seed)
            if values is None:
                unsat.append((job_id, seed))
                continue
            matchings = tuple(
                complement_matching(values, left, right)
                for left, right in ((0, 1), (0, 2), (1, 2))
            )
            cycle_type = holonomy_cycle_type(matchings)
            histogram[cycle_type] += 1
            if not args.quiet:
                print(job_id, seed, matchings, cycle_type)
    print("jobs", len(job_ids), "seeds", args.seeds, "unsat", len(unsat))
    print("holonomy_cycle_type_histogram", dict(histogram))
    return 1 if unsat else 0


if __name__ == "__main__":
    raise SystemExit(main())
