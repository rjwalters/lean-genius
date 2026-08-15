#!/usr/bin/env python3
"""Emit the 14 canonical h=7 order-49 classified CNFs.

The high supports are determined by a linear triple system on seven points.
This recovers the original classified-sweep encoding, but canonicalizes under
all 7! high-point relabelings before emitting instances.
"""

import argparse
import hashlib
import itertools
import json
from pathlib import Path

from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool

High = tuple[int, ...]
System = tuple[High, ...]
POINTS = tuple(range(7))
ALL_TRIPLES = tuple(itertools.combinations(POINTS, 3))
EXPECTED_COUNTS = (1, 1, 2, 3, 3, 2, 1, 1)


def linear(left: High, right: High) -> bool:
    return len(set(left) & set(right)) <= 1


def normalized_systems(size: int) -> list[System]:
    if size == 0:
        return [()]
    output: list[System] = []

    def visit(system: list[High], start: int) -> None:
        if len(system) == size:
            degrees = [sum(point in triple for triple in system) for point in POINTS]
            if max(degrees) <= 3:
                output.append(tuple(system))
            return
        for index in range(start, len(ALL_TRIPLES)):
            triple = ALL_TRIPLES[index]
            if all(linear(triple, prior) for prior in system):
                visit(system + [triple], index + 1)

    # Every nonempty system can be relabeled so its first triple is 012.
    visit([(0, 1, 2)], 1)
    return output


def relabel(system: System, permutation: tuple[int, ...]) -> System:
    return tuple(
        sorted(tuple(sorted(permutation[point] for point in triple)) for triple in system)
    )


def canonical(system: System) -> System:
    return min(relabel(system, permutation) for permutation in itertools.permutations(POINTS))


def canonical_systems(size: int) -> list[System]:
    return sorted({canonical(system) for system in normalized_systems(size)})


def support_map(system: System) -> dict[int, set[int]]:
    internal_pairs = {
        pair for triple in system for pair in itertools.combinations(triple, 2)
    }
    noninternal_pairs = [
        pair for pair in itertools.combinations(POINTS, 2) if pair not in internal_pairs
    ]
    supports: dict[int, set[int]] = {}
    vertex = 7
    for triple in system:
        supports[vertex] = set(triple)
        vertex += 1
    for pair in noninternal_pairs:
        supports[vertex] = set(pair)
        vertex += 1
    triple_degrees = [sum(point in triple for triple in system) for point in POINTS]
    for point in POINTS:
        for _ in range(triple_degrees[point] + 2):
            supports[vertex] = {point}
            vertex += 1
    while vertex < 49:
        supports[vertex] = set()
        vertex += 1
    if vertex != 49:
        raise AssertionError("profile census exceeded 49 vertices")
    return supports


def build(system: System) -> CNF:
    order, high_count = 49, 7
    supports = support_map(system)
    pool = IDPool()

    def edge(i: int, j: int) -> int:
        a, b = min(i, j), max(i, j)
        return pool.id(("e", a, b))

    clauses: list[list[int]] = []
    for a, b in itertools.combinations(POINTS, 2):
        clauses.append([-edge(a, b)])
    for low in range(high_count, order):
        for high in POINTS:
            clauses.append([edge(low, high)] if high in supports[low] else [-edge(low, high)])

    for i, j in itertools.combinations(range(order), 2):
        others = [w for w in range(order) if w != i and w != j]
        for w, w2 in itertools.combinations(others, 2):
            clauses.append(
                [-edge(i, w), -edge(j, w), -edge(i, w2), -edge(j, w2)]
            )

    for vertex in range(order):
        incident = [edge(vertex, other) for other in range(order) if other != vertex]
        clauses.extend(
            CardEnc.equals(
                lits=incident,
                bound=8 if vertex < high_count else 7,
                vpool=pool,
                encoding=EncType.seqcounter,
            ).clauses
        )

    neighborhoods = {
        high: [low for low in range(high_count, order) if high in supports[low]]
        for high in POINTS
    }
    if any(len(neighborhoods[high]) != 8 for high in POINTS):
        raise AssertionError("high code does not have size eight")
    for low in range(high_count, order):
        for high in POINTS:
            clauses.append(
                [edge(low, member) for member in neighborhoods[high] if member != low]
            )
    return CNF(from_clauses=clauses)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output_dir", type=Path)
    parser.add_argument("--list-only", action="store_true")
    args = parser.parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    manifest = []
    counts = tuple(len(canonical_systems(size)) for size in range(8))
    if counts != EXPECTED_COUNTS:
        raise AssertionError(f"canonical census mismatch: {counts}")
    for size in range(8):
        for index, system in enumerate(canonical_systems(size)):
            name = f"h7_t{size}_rep{index}"
            row = {"name": name, "t": size, "rep": index, "system": system}
            if not args.list_only:
                path = args.output_dir / f"{name}.cnf"
                build(system).to_file(path)
                row["sha256"] = hashlib.sha256(path.read_bytes()).hexdigest()
            manifest.append(row)
            print(json.dumps(row, separators=(",", ":")))
    (args.output_dir / "h7_canonical_manifest.json").write_text(
        json.dumps(manifest, indent=2) + "\n"
    )


if __name__ == "__main__":
    main()
