#!/usr/bin/env python3
"""Reproduce the order-48 witness non-isomorphism comparison.

The comparison archive is the Afzaly--McKay C4 table downloaded from
https://users.cecs.anu.edu.au/~bdm/data/extremal/c4_n48e168.maybe.s6
on 2026-08-31.  Its expected SHA-256 pins the exact external input.
"""

from __future__ import annotations

import argparse
import hashlib
import re
from pathlib import Path

import networkx as nx


HERE = Path(__file__).resolve().parent
ARCHIVE_SHA256 = "7bc1de35449c8eee0133cecf38d6ed9875d7412f4c952aa50157f2beb96484c9"
LEAN_SOURCE = HERE.parents[3] / "proofs" / "Proofs" / "Erdos85Boza48Witness.lean"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_one_sparse6(path: Path) -> nx.Graph:
    lines = path.read_bytes().splitlines()
    if len(lines) != 1:
        raise ValueError(f"expected one sparse6 graph in {path}, found {len(lines)}")
    return nx.from_sparse6_bytes(lines[0])


def read_lean_edges(path: Path) -> set[tuple[int, int]]:
    source = path.read_text()
    match = re.search(
        r"def boza48Edges : List \(Nat × Nat\) := \[(.*?)\n\]", source, re.S
    )
    if match is None:
        raise ValueError("could not locate boza48Edges in the Lean source")
    return {
        (int(left), int(right))
        for left, right in re.findall(r"\((\d+), (\d+)\)", match.group(1))
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--witness", type=Path, default=HERE / "data" / "boza48_witness.s6"
    )
    parser.add_argument(
        "--archive", type=Path,
        default=HERE / "data" / "c4_n48e168.maybe.s6",
    )
    parser.add_argument("--lean-source", type=Path, default=LEAN_SOURCE)
    args = parser.parse_args()

    if sha256(args.archive) != ARCHIVE_SHA256:
        raise ValueError("Afzaly--McKay archive SHA-256 mismatch")

    witness = read_one_sparse6(args.witness)
    lean_edges = read_lean_edges(args.lean_source)
    archive = [nx.from_sparse6_bytes(line)
               for line in args.archive.read_bytes().splitlines()]
    if (witness.number_of_nodes(), witness.number_of_edges()) != (48, 168):
        raise ValueError("checked witness does not have order 48 and size 168")
    if set(dict(witness.degree()).values()) != {7}:
        raise ValueError("checked witness is not 7-regular")
    if set(witness.edges()) != lean_edges:
        raise ValueError("witness sparse6 does not match Lean boza48Edges exactly")
    if len(archive) != 10:
        raise ValueError(f"expected ten archived graphs, found {len(archive)}")
    if any((graph.number_of_nodes(), graph.number_of_edges()) != (48, 168)
           for graph in archive):
        raise ValueError("archive contains a graph outside order 48 and size 168")

    regular_indices = [
        index for index, graph in enumerate(archive)
        if set(dict(graph.degree()).values()) == {7}
    ]
    if regular_indices != [9]:
        raise ValueError(f"expected archived graph #9 to be uniquely regular: {regular_indices}")

    comparisons = [nx.is_isomorphic(witness, graph) for graph in archive]
    if any(comparisons):
        raise ValueError(f"witness matches archive indices: "
                         f"{[i for i, value in enumerate(comparisons) if value]}")

    print("PASS: witness is non-isomorphic to all 10 Afzaly--McKay archive graphs")
    print(f"archive_sha256={ARCHIVE_SHA256}")
    print("unique_7_regular_archive_index=9")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
