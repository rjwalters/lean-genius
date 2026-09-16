#!/usr/bin/env python3
"""Audit the exact Lean edge lists behind the order-48/49 finite witnesses.

This is an independent integer/bitset check, not a Lean kernel proof.
"""
from __future__ import annotations

from collections import Counter
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[4]
SOURCES = (
    ("boza48Edges", 48, "Erdos85Boza48Witness.lean",
     "a3b4b67fc6e47c0e4bba7a239b75fb5d57407132af88c9133dd00bc19d0fcc73",
     {7: 48}),
    ("orderFortyNineDegreeSixEdges", 49,
     "Erdos85OrderFortyNineDegreeSixWitness.lean",
     "6cc9c63f666817e3664cac2d7e09408c6a5d92818ba729b61ebddfdcbea06db4",
     {6: 7, 7: 42}),
)


def read_edges(path: Path, name: str, expected_sha: str) -> list[tuple[int, int]]:
    raw = path.read_bytes()
    if hashlib.sha256(raw).hexdigest() != expected_sha:
        raise ValueError(f"Lean source changed: {path}")
    source = raw.decode()
    match = re.search(rf"def {name} : List \(Nat × Nat\) :=\s*\[(.*?)\]", source, re.S)
    if match is None:
        raise ValueError(f"Lean edge definition missing: {name}")
    body = match.group(1)
    pattern = r"\(\s*(\d+)\s*,\s*(\d+)\s*\)"
    edges = [(int(u), int(v)) for u, v in re.findall(pattern, body)]
    if re.sub(pattern, "", body).replace(",", "").strip():
        raise ValueError(f"Unparsed Lean edge-list syntax: {name}")
    return edges


def audit(name: str, order: int, filename: str, source_sha: str,
          expected_degrees: dict[int, int]) -> dict:
    path = ROOT / "proofs/Proofs" / filename
    edges = read_edges(path, name, source_sha)
    if len(edges) != 168 or len(set(edges)) != 168 or any(
            not 0 <= u < v < order for u, v in edges):
        raise ValueError(f"Not 168 distinct simple ordered edges: {name}")
    neighbors = [0] * order
    for u, v in edges:
        neighbors[u] |= 1 << v
        neighbors[v] |= 1 << u
    degrees = dict(sorted(Counter(mask.bit_count() for mask in neighbors).items()))
    if degrees != expected_degrees:
        raise ValueError(f"Unexpected degree distribution: {name}: {degrees}")
    pair_counts = Counter((neighbors[u] & neighbors[v]).bit_count()
                          for u in range(order) for v in range(u + 1, order))
    if sum(pair_counts.values()) != order * (order - 1) // 2 or max(pair_counts) > 1:
        raise ValueError(f"A pair has two common neighbors, hence a C4: {name}")
    return {"name": name, "source": str(path), "source_sha256": source_sha,
            "order": order, "edges": len(edges),
            "degree_distribution": degrees,
            "distinct_vertex_pairs": order * (order - 1) // 2,
            "common_neighbor_count_distribution": dict(sorted(pair_counts.items())),
            "maximum_pair_common_neighbors": max(pair_counts),
            "c4_count_from_pair_formula": sum(n * (n - 1) // 2 * count
                                               for n, count in pair_counts.items()) // 2}


def main() -> None:
    rows = [audit(*source) for source in SOURCES]
    if any(row["c4_count_from_pair_formula"] != 0 for row in rows):
        raise ValueError("A four-cycle was counted")
    print(json.dumps({"schema": "erdos85-finite-witness-edge-audit-v1",
                      "scope": "Independent exact edge-list arithmetic; no Lean proof",
                      "rows": rows}, indent=2))


if __name__ == "__main__":
    main()
