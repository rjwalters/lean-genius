#!/usr/bin/env python3
"""Audit the 7-adic determinant on B1-constrained defect completions.

For each canonical propagated sixth state, a pair of ordinary vertices is a
forced defect edge when every possible common-neighbour witness is blocked,
and a forced defect nonedge when a positive witness is already present.  The
remaining defect edges are completed subject only to their exact degrees.
This deliberately weak relaxation tests how much of the determinant filter is
already visible before completing the original graph.
"""

from __future__ import annotations

import argparse
import json
import math
import re
import subprocess
from collections import Counter
from pathlib import Path

import networkx as nx

from analyze_small_high_adaptive_sixth_orbits import propagated_graph
from analyze_small_high_adaptive_sixth_root_partitions import canonical_job_ids
from analyze_small_high_adaptive_sixth_units import (
    build_falsified_occurrences,
    manifest_jobs,
    read_dimacs,
)
from audit_order49_defect_determinant import determinant_expression


ORDINARY = tuple(range(3, 49))


def edge(u: int, v: int) -> tuple[int, int]:
    return (u, v) if u < v else (v, u)


def signed_edges(graph: nx.Graph) -> tuple[set[tuple[int, int]], set[tuple[int, int]]]:
    positive = set()
    negative = set()
    for u, v, data in graph.edges(data=True):
        (positive if data["state"] == "1" else negative).add(edge(u, v))
    return positive, negative


def defect_smt(
    graph: nx.Graph, blocked: list[frozenset[tuple[int, int]]]
) -> tuple[str, list[tuple[int, int]]]:
    positive, negative = signed_edges(graph)
    pairs = [(u, v) for u in ORDINARY for v in ORDINARY if u < v]
    lines = [
        "(set-logic QF_LIA)",
    ]
    lines.extend(f"(declare-const d_{u}_{v} Bool)" for u, v in pairs)

    for u, v in pairs:
        witnesses = [w for w in range(49) if w not in (u, v)]
        if any(edge(u, w) in positive and edge(v, w) in positive for w in witnesses):
            lines.append(f"(assert (not d_{u}_{v}))")
        elif all(edge(u, w) in negative or edge(v, w) in negative for w in witnesses):
            lines.append(f"(assert d_{u}_{v})")

    for u in ORDINARY:
        high_incidence = sum(edge(root, u) in positive for root in range(3))
        target = 6 - high_incidence
        terms = [
            f"(ite d_{min(u, v)}_{max(u, v)} 1 0)"
            for v in ORDINARY
            if v != u
        ]
        lines.append(f"(assert (= (+ {' '.join(terms)}) {target}))")
    for previous in blocked:
        difference = [
            f"(not d_{u}_{v})" if (u, v) in previous else f"d_{u}_{v}"
            for u, v in pairs
        ]
        lines.append(f"(assert (or {' '.join(difference)}))")
    lines.extend([
        "(check-sat)",
        "(get-value (" + " ".join(f"d_{u}_{v}" for u, v in pairs) + "))",
    ])
    return "\n".join(lines) + "\n", pairs


def solve_defect(
    graph: nx.Graph, blocked: list[frozenset[tuple[int, int]]], timeout: int
) -> tuple[nx.Graph, frozenset[tuple[int, int]]] | None:
    smt, pairs = defect_smt(graph, blocked)
    completed = subprocess.run(
        ["z3", "-in", f"-T:{timeout}"], input=smt, text=True,
        capture_output=True, check=False,
    )
    if completed.stdout.startswith("unsat"):
        return None
    if not completed.stdout.startswith("sat"):
        raise RuntimeError(completed.stdout.strip() or completed.stderr.strip())
    values = {
        (int(u), int(v)): value == "true"
        for u, v, value in re.findall(r"\(d_(\d+)_(\d+)\s+(true|false)\)", completed.stdout)
    }
    if len(values) != len(pairs):
        raise AssertionError(f"parsed {len(values)} of {len(pairs)} defect variables")
    result = nx.Graph()
    result.add_nodes_from(range(len(ORDINARY)))
    result.add_edges_from((u - 3, v - 3) for (u, v), present in values.items() if present)
    signature = frozenset(pair for pair, present in values.items() if present)
    return result, signature


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--orbits", type=Path, required=True)
    parser.add_argument("--limit", type=int)
    parser.add_argument("--completions", type=int, default=1)
    parser.add_argument("--timeout", type=int, default=30)
    args = parser.parse_args()

    manifest = json.loads(args.manifest.read_text())
    orbit_report = json.loads(args.orbits.read_text())
    jobs = dict(manifest_jobs(manifest))
    job_ids = canonical_job_ids(orbit_report)
    if args.limit is not None:
        job_ids = job_ids[:args.limit]
    bases = {Path(leaf["base"]) for leaf in manifest["leaves"].values()}
    if len(bases) != 1:
        raise ValueError("expected one shared base CNF")
    _variables, clauses = read_dimacs(next(iter(bases)))
    occurrences = build_falsified_occurrences(clauses)
    base_units = tuple(clause[0] for clause in clauses if len(clause) == 1)

    counts: Counter[str] = Counter()
    residues: Counter[int] = Counter()
    for job_id in job_ids:
        state = propagated_graph(clauses, occurrences, base_units, jobs[job_id])
        blocked: list[frozenset[tuple[int, int]]] = []
        for _ in range(args.completions):
            solved = solve_defect(state, blocked, args.timeout)
            if solved is None:
                counts["unsat"] += 1
                break
            defect, signature = solved
            blocked.append(signature)
            counts["sat"] += 1
            if nx.is_connected(defect):
                counts["connected"] += 1
            value = determinant_expression(defect)
            residues[value % 49] += 1
            if value % 49:
                continue
            counts["divisible_by_49"] += 1
            quotient = value // 49
            if quotient >= 0 and math.isqrt(quotient) ** 2 == quotient:
                counts["forty_nine_times_square"] += 1

    print("jobs", len(job_ids), "completions", args.completions, dict(counts))
    print("residues_mod_49", dict(sorted(residues.items())))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
