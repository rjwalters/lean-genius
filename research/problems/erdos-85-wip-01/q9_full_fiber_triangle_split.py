#!/usr/bin/env python3
"""Classify the full-fiber obstruction by triangles in the U1 graph K.

Every tested outer design has a strict unit-row-price full-fiber certificate.
Moreover, whenever K contains a triangle, at least one triangle vertex itself
supports such a certificate.  This motivates a structural split between a
triangle-local cover lemma and a genuinely fractional triangle-free lemma.
The checks here are exact certificate regressions, not a uniform proof.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from q9_symmetric_point_mass_obstruction import (
    fixed_system,
    random_outer,
    unit_nondiagonal_fiber_certificate,
)


HERE = Path(__file__).resolve().parent
SERIOUS = (
    "q9_13f_counterexample.json",
    "q9_13t_counterexample.json",
    "q9_gram_fractional_gap_witness.json",
    "q9_branch4_row40_interval_witness.json",
)


def classify(name: str, payload: dict) -> dict:
    system = fixed_system(payload)
    edges = {tuple(sorted(edge)) for edge in payload["k_edges"]}
    neighbors = [set() for _ in range(24)]
    for u, v in edges:
        neighbors[u].add(v)
        neighbors[v].add(u)
    triangle_vertices = {
        p for p in range(24)
        if any(tuple(sorted((u, v))) in edges
               for u in neighbors[p] for v in neighbors[p] if u < v)
    }
    successful = {
        p for p in range(24)
        if unit_nondiagonal_fiber_certificate(
            system, p, include_diagonal=True) is not None
    }
    if not successful:
        raise RuntimeError(f"{name}: no strict full-fiber certificate")
    if triangle_vertices and not triangle_vertices & successful:
        raise RuntimeError(
            f"{name}: triangles exist but no triangle vertex succeeds")
    return {
        "name": name,
        "branch": system["branch"],
        "triangle_vertices": sorted(triangle_vertices),
        "successful_points": sorted(successful),
        "successful_triangle_vertices": sorted(
            triangle_vertices & successful),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--random-seeds", type=int, default=0)
    parser.add_argument("--timeout-seconds", type=int, default=60)
    args = parser.parse_args()
    if args.random_seeds < 0:
        parser.error("--random-seeds must be nonnegative")

    records = [
        classify(name, json.loads((HERE / name).read_text()))
        for name in SERIOUS
    ]
    for branch in (3, 4):
        for seed in range(args.random_seeds):
            payload = random_outer(branch, seed, args.timeout_seconds)
            records.append(classify(
                f"random-branch{branch}-seed{seed}", payload))

    summary = {
        "models": len(records),
        "triangle_models": sum(bool(item["triangle_vertices"])
                               for item in records),
        "triangle_models_with_successful_triangle_vertex": sum(
            bool(item["successful_triangle_vertices"]) for item in records
        ),
        "triangle_free_models": sum(not item["triangle_vertices"]
                                    for item in records),
        "all_models_have_strict_full_fiber": True,
    }
    print(json.dumps({"records": records, "summary": summary},
                     indent=2, sort_keys=True))
    print("full_fiber_triangle_split=EXACT_CORPUS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
