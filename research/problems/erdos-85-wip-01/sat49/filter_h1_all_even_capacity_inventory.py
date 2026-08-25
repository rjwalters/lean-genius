#!/usr/bin/env python3
"""Export the exact 2,503-row all-even capacity inventory.

This mirrors the Lean list ``oneHighAllEvenCapacityInventoryTables``:

* retain rows satisfying ``oneHighTableCrossMissCapacity``; and
* retain rows for which the eight source pairing choices have a combined
  off-diagonal parity mask equal to zero.

The optional seven-field jobs output is accepted by the existing exact-v2
runner and by ``generate_h1_v2_lean_stubs.py --terminal-jobs``.  Rows remain
in authoritative compact-inventory order, hence their position within each
profile is the terminal-local Lean list index.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from filter_h1_capacity_inventory import (
    TABLE_PAIRS,
    has_cross_miss_capacity,
    worker_tag,
)


PROFILE_NAMES = ("BBBB", "ABBB", "AABB", "AAAB", "AAAA")
EXPECTED_COUNTS = (609, 16, 1587, 6, 285)


def table_get(values: tuple[int, ...], source: int, label: int) -> int:
    pair = (min(source, label), max(source, label))
    try:
        return values[TABLE_PAIRS.index(pair)]
    except ValueError:
        return 0


def internal_edges(profile: int, source: int) -> int:
    """Numeric copy of ``oneHighFamilyInternalEdges``."""
    return 1 if source % 2 == 0 and source // 2 < profile else 2


def source_pairing_masks(
    profile: int, values: tuple[int, ...], source: int
) -> set[int]:
    endpoints = tuple(
        label
        for label in range(8)
        for _ in range(table_get(values, source, label))
    )
    if len(endpoints) != 2 * internal_edges(profile, source):
        return set()

    def pair_masks(remaining: tuple[int, ...]) -> set[int]:
        if not remaining:
            return {0}
        first = remaining[0]
        masks: set[int] = set()
        for index in range(1, len(remaining)):
            second = remaining[index]
            rest = remaining[1:index] + remaining[index + 1 :]
            left, right = sorted((first, second))
            bit = 1 << (8 * left + right)
            masks.update(bit ^ suffix for suffix in pair_masks(rest))
        return masks

    return pair_masks(endpoints)


OFF_DIAGONAL_MASK = sum(
    1 << (8 * left + right)
    for left in range(8)
    for right in range(left + 1, 8)
)


def has_all_even_pairing(profile: int, values: tuple[int, ...]) -> bool:
    states = {0}
    for source in range(8):
        choices = source_pairing_masks(profile, values, source)
        if not choices:
            return False
        states = {state ^ choice for state in states for choice in choices}
    return any(state & OFF_DIAGONAL_MASK == 0 for state in states)


def table_record(values: tuple[int, ...]) -> list[list[object]]:
    return [
        [[left, right], value]
        for (left, right), value in zip(TABLE_PAIRS, values, strict=True)
        if value != 0
    ]


def main() -> None:
    script = Path(__file__).resolve()
    repo = script.parents[4]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--inventory",
        type=Path,
        default=repo / "proofs/Proofs/Certificates/h1_orbit_inventory.compact",
    )
    parser.add_argument("--manifest-output", type=Path)
    parser.add_argument("--lean-exact-jobs-output", type=Path)
    parser.add_argument("--summary-only", action="store_true")
    args = parser.parse_args()

    selected: list[list[tuple[str, tuple[int, ...]]]] = [[] for _ in range(5)]
    seen: set[str] = set()
    for line_number, raw in enumerate(args.inventory.read_text().splitlines(), 1):
        fields = raw.split()
        if not fields:
            continue
        profile, *raw_values = map(int, fields)
        values = tuple(raw_values)
        if profile not in range(5) or len(values) != len(TABLE_PAIRS):
            raise ValueError(f"{args.inventory}:{line_number}: malformed row")
        if has_cross_miss_capacity(values) and has_all_even_pairing(profile, values):
            tag = worker_tag(values)
            if tag in seen:
                raise ValueError(f"duplicate selected worker tag: {tag}")
            seen.add(tag)
            selected[profile].append((tag, values))

    counts = tuple(map(len, selected))
    if counts != EXPECTED_COUNTS:
        raise ValueError(f"expected counts {EXPECTED_COUNTS}, found {counts}")

    if args.manifest_output:
        args.manifest_output.parent.mkdir(parents=True, exist_ok=True)
        args.manifest_output.write_text(
            "".join(
                f"{tag}\t{profile}\t{PROFILE_NAMES[profile]}\t{local_index}"
                f"\t{' '.join(map(str, values))}\n"
                for profile, rows in enumerate(selected)
                for local_index, (tag, values) in enumerate(rows)
            )
        )

    if args.lean_exact_jobs_output:
        args.lean_exact_jobs_output.parent.mkdir(parents=True, exist_ok=True)
        table_dir = args.lean_exact_jobs_output.parent / "tables"
        table_dir.mkdir(parents=True, exist_ok=True)
        jobs: list[str] = []
        for profile, rows in enumerate(selected):
            for tag, values in rows:
                table_path = table_dir / f"{tag}.table"
                table_path.write_text(json.dumps(table_record(values)) + "\n")
                jobs.append(
                    "\t".join(
                        (tag, str(profile), PROFILE_NAMES[profile], "MONO",
                         str(table_path), "", "")
                    )
                )
        args.lean_exact_jobs_output.write_text("".join(job + "\n" for job in jobs))

    if not args.summary_only:
        print("profile\tlocal_index\ttag\ttable_values")
        for profile, rows in enumerate(selected):
            for local_index, (tag, values) in enumerate(rows):
                print(
                    f"{profile}\t{local_index}\t{tag}\t"
                    f"{' '.join(map(str, values))}"
                )
    total = sum(counts)
    print(f"# counts={list(counts)} total={total}")


if __name__ == "__main__":
    main()
