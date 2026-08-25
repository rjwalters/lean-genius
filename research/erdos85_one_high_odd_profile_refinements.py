#!/usr/bin/env python3
"""Export exact all-even pairing refinements for one-high profiles 1 and 3.

The compact H1 inventory stores miss-count tables, while the structural CSP
consumes the row pairings chosen by ``oneHighPairingRefinements``.  This
script mirrors that Lean construction: expand each row's endpoint multiset,
enumerate its unordered pairings, canonicalize and sort the pairs, take the
eight-row product, and retain precisely the globally even refinements.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

SCRIPT = Path(__file__).resolve()
REPO = SCRIPT.parents[1]
SAT49 = REPO / "research/problems/erdos-85-wip-01/sat49"
sys.path.insert(0, str(SAT49))

from filter_h1_all_even_capacity_inventory import (  # noqa: E402
    EXPECTED_COUNTS,
    internal_edges,
    table_get,
)
from filter_h1_capacity_inventory import (  # noqa: E402
    TABLE_PAIRS,
    has_cross_miss_capacity,
    worker_tag,
)

ODD_PROFILES = (1, 3)


Pair = tuple[int, int]
Row = tuple[Pair, ...]
Refinement = tuple[Row, ...]


def row_pairings(endpoints: tuple[int, ...]) -> tuple[Row, ...]:
    """All canonical sorted pairings of one endpoint multiset."""
    if not endpoints:
        return ((),)
    first = endpoints[0]
    results: set[Row] = set()
    for index in range(1, len(endpoints)):
        second = endpoints[index]
        rest = endpoints[1:index] + endpoints[index + 1 :]
        pair = (min(first, second), max(first, second))
        for suffix in row_pairings(rest):
            results.add(tuple(sorted((pair,) + suffix)))
    return tuple(sorted(results))


def table_rows(profile: int, values: tuple[int, ...]) -> tuple[tuple[Row, ...], ...]:
    rows = []
    for source in range(8):
        endpoints = tuple(
            label
            for label in range(8)
            for _ in range(table_get(values, source, label))
        )
        if len(endpoints) != 2 * internal_edges(profile, source):
            return ()
        rows.append(row_pairings(endpoints))
    return tuple(rows)


def pair_bit(pair: Pair) -> int:
    # Lean's all-even predicate deliberately ignores diagonal label pairs.
    return 0 if pair[0] == pair[1] else 1 << (8 * pair[0] + pair[1])


def even_refinements(profile: int, values: tuple[int, ...]) -> tuple[Refinement, ...]:
    choices = table_rows(profile, values)
    if not choices:
        return ()
    results: list[Refinement] = []

    def visit(source: int, parity: int, chosen: list[Row]) -> None:
        if source == 8:
            if parity == 0:
                results.append(tuple(chosen))
            return
        for row in choices[source]:
            row_parity = 0
            for pair in row:
                row_parity ^= pair_bit(pair)
            chosen.append(row)
            visit(source + 1, parity ^ row_parity, chosen)
            chosen.pop()

    visit(0, 0, [])
    return tuple(results)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--inventory",
        type=Path,
        default=REPO / "proofs/Proofs/Certificates/h1_orbit_inventory.compact",
    )
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--manifest", type=Path)
    args = parser.parse_args()

    selected_tables = {profile: 0 for profile in ODD_PROFILES}
    records: list[dict[str, object]] = []
    for line_number, raw in enumerate(args.inventory.read_text().splitlines(), 1):
        fields = raw.split()
        if not fields:
            continue
        profile, *raw_values = map(int, fields)
        if profile not in ODD_PROFILES:
            continue
        values = tuple(raw_values)
        if len(values) != len(TABLE_PAIRS):
            raise ValueError(f"{args.inventory}:{line_number}: malformed row")
        if not has_cross_miss_capacity(values):
            continue
        refinements = even_refinements(profile, values)
        if not refinements:
            continue
        selected_tables[profile] += 1
        tag = worker_tag(values)
        for local_index, refinement in enumerate(refinements):
            records.append({
                "profile": profile,
                "table_tag": tag,
                "refinement_index": local_index,
                "refinement": refinement,
            })

    for profile in ODD_PROFILES:
        expected = EXPECTED_COUNTS[profile]
        if selected_tables[profile] != expected:
            raise ValueError(
                f"profile {profile}: expected {expected} selected tables, "
                f"found {selected_tables[profile]}"
            )

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps([r["refinement"] for r in records]) + "\n")
    if args.manifest:
        args.manifest.parent.mkdir(parents=True, exist_ok=True)
        args.manifest.write_text("".join(
            json.dumps({k: v for k, v in record.items() if k != "refinement"},
                       separators=(",", ":")) + "\n"
            for record in records
        ))
    counts = {profile: sum(r["profile"] == profile for r in records)
              for profile in ODD_PROFILES}
    print(json.dumps({"tables": selected_tables, "refinements": counts},
                     separators=(",", ":")))


if __name__ == "__main__":
    main()
