#!/usr/bin/env python3
"""Filter the PSV cubic vertex-transitive census for q=9 shadows.

The input is the graph6/sparse6 conversion of the Potočnik--Spiga--Verret
census at

  https://github.com/kguo-sagecode/cubic-vertextransitive-graphs

pinned to commit 68c592d4790ab1737f04d86d3102c4999bbc6c09.  Run with

  python3 q9_cubic_shadow_census.py cubicvt4-300g6.txt

The only non-stdlib dependency is NetworkX, used to decode sparse6.  Girth is
computed here by an independent breadth-first search rather than delegated to
NetworkX.
"""

from __future__ import annotations

import argparse
import hashlib
from collections import Counter, defaultdict, deque
from pathlib import Path

import networkx as nx


EXPECTED_SHA256 = "4bac89beec1465265318266117c38a2c1680e73a21efd322411207cef5313088"
COMPONENT_ORDERS = (4, 8, 10, 16, 20, 40, 80)
EXPECTED_SURVIVORS = {
    4: [],
    8: [],
    10: [3],
    16: [4],
    20: [4, 6, 7],
    40: [3, 4, 5, 6, 7, 8, 11],
    80: [
        2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 14, 15, 16,
        17, 18, 19, 20, 21, 23, 24, 28, 29, 30, 32, 33,
    ],
}


def girth(graph: nx.Graph) -> int | None:
    """Return the length of a shortest cycle by repeated BFS."""
    best = len(graph) + 1
    for root in graph:
        distance = {root: 0}
        parent = {root: None}
        queue = deque([root])
        while queue:
            u = queue.popleft()
            for v in graph[u]:
                if v not in distance:
                    distance[v] = distance[u] + 1
                    parent[v] = u
                    queue.append(v)
                elif parent[u] != v:
                    best = min(best, distance[u] + distance[v] + 1)
    return None if best == len(graph) + 1 else best


def decode(line: bytes) -> nx.Graph:
    return (
        nx.from_sparse6_bytes(line)
        if line.startswith(b":")
        else nx.from_graph6_bytes(line)
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("census", type=Path)
    parser.add_argument(
        "--allow-unpinned-input",
        action="store_true",
        help="run on a file whose SHA-256 differs from the pinned census",
    )
    args = parser.parse_args()

    raw = args.census.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    if digest != EXPECTED_SHA256 and not args.allow_unpinned_input:
        raise SystemExit(
            f"unexpected census SHA-256: {digest}; expected {EXPECTED_SHA256}"
        )

    totals: Counter[int] = Counter()
    survivors: dict[int, list[int]] = defaultdict(list)
    girths: dict[int, Counter[int | None]] = defaultdict(Counter)

    for line_number, raw_line in enumerate(raw.splitlines(), start=1):
        line = raw_line.strip()
        if not line:
            continue
        graph = decode(line)
        order = len(graph)
        if order not in COMPONENT_ORDERS:
            continue
        totals[order] += 1
        ordinal = totals[order]

        assert nx.is_connected(graph), (line_number, "disconnected census entry")
        assert set(dict(graph.degree()).values()) == {3}, (
            line_number,
            "non-cubic census entry",
        )
        graph_girth = girth(graph)
        girths[order][graph_girth] += 1
        if graph_girth is not None and graph_girth >= 5:
            survivors[order].append(ordinal)

    actual = {order: survivors[order] for order in COMPONENT_ORDERS}
    if digest == EXPECTED_SHA256:
        assert actual == EXPECTED_SURVIVORS, (actual, EXPECTED_SURVIVORS)

    print(f"sha256 {digest}")
    print("order copies total survivor_ordinals girth_distribution")
    for order in COMPONENT_ORDERS:
        distribution = ",".join(
            f"{cycle_length}:{count}"
            for cycle_length, count in sorted(girths[order].items())
        )
        ordinals = ",".join(map(str, survivors[order])) or "-"
        print(
            order,
            80 // order,
            totals[order],
            ordinals,
            distribution,
        )
    print(f"shadow_types {sum(map(len, survivors.values()))}")


if __name__ == "__main__":
    main()
