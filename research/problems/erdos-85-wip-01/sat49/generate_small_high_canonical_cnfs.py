#!/usr/bin/env python3
"""Emit canonical base CNFs for the h=3 and h=5 order-49 strata.

The h=5 outputs are the complete classified instances.  The two historical
h=3 scout instances append 84/108 pinning clauses to these base segments;
this script deliberately emits the common semantic base before those WLOG
pins so its output mirrors `orderFortyNineGeneratedCanonicalSatCnf`.
"""

import argparse
import hashlib
import itertools
import json
from pathlib import Path

from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool


SYSTEMS = {
    3: ((), ((0, 1, 2),)),
    5: ((), ((0, 1, 2),), ((0, 1, 2), (0, 3, 4))),
}


def support_map(high_count: int, system: tuple[tuple[int, ...], ...]):
    points = tuple(range(high_count))
    internal_pairs = {
        pair for triple in system for pair in itertools.combinations(triple, 2)
    }
    supports: dict[int, set[int]] = {}
    vertex = high_count
    for triple in system:
        supports[vertex] = set(triple)
        vertex += 1
    for pair in itertools.combinations(points, 2):
        if pair not in internal_pairs:
            supports[vertex] = set(pair)
            vertex += 1
    for point in points:
        triple_degree = sum(point in triple for triple in system)
        for _ in range(9 - high_count + triple_degree):
            supports[vertex] = {point}
            vertex += 1
    while vertex < 49:
        supports[vertex] = set()
        vertex += 1
    if vertex != 49:
        raise AssertionError("profile census exceeded 49 vertices")
    return supports


def build(high_count: int, system: tuple[tuple[int, ...], ...]) -> CNF:
    order = 49
    points = tuple(range(high_count))
    supports = support_map(high_count, system)
    pool = IDPool()

    def edge(i: int, j: int) -> int:
        return pool.id(("e", min(i, j), max(i, j)))

    clauses: list[list[int]] = []
    for a, b in itertools.combinations(points, 2):
        clauses.append([-edge(a, b)])
    for low in range(high_count, order):
        for high in points:
            literal = edge(low, high)
            clauses.append([literal] if high in supports[low] else [-literal])
    for i, j in itertools.combinations(range(order), 2):
        others = [w for w in range(order) if w != i and w != j]
        for w, w2 in itertools.combinations(others, 2):
            clauses.append(
                [-edge(i, w), -edge(j, w), -edge(i, w2), -edge(j, w2)]
            )
    for vertex in range(order):
        incident = [edge(vertex, other) for other in range(order) if other != vertex]
        clauses.extend(CardEnc.equals(
            lits=incident,
            bound=8 if vertex < high_count else 7,
            vpool=pool,
            encoding=EncType.seqcounter,
        ).clauses)
    neighborhoods = {
        high: [low for low in range(high_count, order) if high in supports[low]]
        for high in points
    }
    if any(len(neighborhoods[high]) != 8 for high in points):
        raise AssertionError("high code does not have size eight")
    for low in range(high_count, order):
        for high in points:
            clauses.append([
                edge(low, member)
                for member in neighborhoods[high]
                if member != low
            ])
    return CNF(from_clauses=clauses)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output_dir", type=Path)
    parser.add_argument("--high-count", type=int, choices=sorted(SYSTEMS))
    parser.add_argument("--index", type=int,
                        help="emit only this canonical system index")
    args = parser.parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    manifest = []
    for high_count, systems in SYSTEMS.items():
        if args.high_count is not None and high_count != args.high_count:
            continue
        for index, system in enumerate(systems):
            if args.index is not None and index != args.index:
                continue
            name = f"h{high_count}_t{len(system)}"
            path = args.output_dir / f"{name}.base.cnf"
            build(high_count, system).to_file(path)
            row = {
                "name": name,
                "high_count": high_count,
                "system": system,
                "clauses": sum(1 for _ in path.open("rb")) - 1,
                "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            }
            manifest.append(row)
            print(json.dumps(row, separators=(",", ":")))
    (args.output_dir / "small_high_canonical_manifest.json").write_text(
        json.dumps(manifest, indent=2) + "\n"
    )


if __name__ == "__main__":
    main()
