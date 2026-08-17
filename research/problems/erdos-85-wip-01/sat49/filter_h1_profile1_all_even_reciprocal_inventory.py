#!/usr/bin/env python3
"""Export the exact five-row profile-1 all-even reciprocal inventory.

This mirrors ``oneHighProfileOneHasAllEvenReciprocalSingleton`` in Lean:

* source 0 has a diagonal singleton pairing; and
* some compatible global pairing has even multiplicity on every
  off-diagonal label pair.

The output formats match the profile-3/4 exporter and seed the separate
Lean-exact runner.  CNF and DRAT fields remain blank because the runner emits
and verifies the authoritative exact CNF itself.
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


PROFILE = 1
FAMILY = "ABBB"
EXPECTED = 5


def table_get(values: tuple[int, ...], source: int, label: int) -> int:
    pair = (min(source, label), max(source, label))
    try:
        return values[TABLE_PAIRS.index(pair)]
    except ValueError:
        return 0


def internal_edges(source: int) -> int:
    return 1 if source == 0 else 2


def source_pairing_masks(values: tuple[int, ...], source: int) -> set[int]:
    endpoints = tuple(
        label
        for label in range(8)
        for _ in range(table_get(values, source, label))
    )
    if len(endpoints) != 2 * internal_edges(source):
        return set()

    def pair_masks(remaining: tuple[int, ...]) -> set[int]:
        if not remaining:
            return {0}
        first = remaining[0]
        masks: set[int] = set()
        for index in range(1, len(remaining)):
            second = remaining[index]
            rest = remaining[1:index] + remaining[index + 1 :]
            pair = (min(first, second), max(first, second))
            bit = 1 << (8 * pair[0] + pair[1])
            masks.update(bit ^ suffix for suffix in pair_masks(rest))
        return masks

    return pair_masks(endpoints)


def has_source_zero_diagonal_singleton(values: tuple[int, ...]) -> bool:
    endpoints = [
        label
        for label in range(8)
        for _ in range(table_get(values, 0, label))
    ]
    return len(endpoints) == 2 and endpoints[0] == endpoints[1]


OFF_DIAGONAL_MASK = sum(
    1 << (8 * left + right)
    for left in range(8)
    for right in range(left + 1, 8)
)


def has_all_even_pairing(values: tuple[int, ...]) -> bool:
    states = {0}
    for source in range(8):
        choices = source_pairing_masks(values, source)
        if not choices:
            return False
        states = {state ^ choice for state in states for choice in choices}
    return any(state & OFF_DIAGONAL_MASK == 0 for state in states)


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
    parser.add_argument("--queue-output", type=Path)
    parser.add_argument("--lean-exact-jobs-output", type=Path)
    parser.add_argument("--summary-only", action="store_true")
    args = parser.parse_args()

    selected: list[tuple[str, tuple[int, ...]]] = []
    for line_number, raw in enumerate(args.inventory.read_text().splitlines(), 1):
        fields = raw.split()
        if not fields:
            continue
        profile, *raw_values = map(int, fields)
        values = tuple(raw_values)
        if profile not in range(5) or len(values) != len(TABLE_PAIRS):
            raise ValueError(f"{args.inventory}:{line_number}: malformed row")
        if (
            profile == PROFILE
            and has_cross_miss_capacity(values)
            and has_source_zero_diagonal_singleton(values)
            and has_all_even_pairing(values)
        ):
            selected.append((worker_tag(values), values))

    if len(selected) != EXPECTED:
        raise ValueError(f"expected {EXPECTED} rows, found {len(selected)}")
    if len({tag for tag, _ in selected}) != EXPECTED:
        raise ValueError("selected rows do not have unique worker tags")

    if args.manifest_output:
        args.manifest_output.parent.mkdir(parents=True, exist_ok=True)
        args.manifest_output.write_text(
            "".join(
                f"{tag}\t{PROFILE}\t{FAMILY}\t{' '.join(map(str, values))}\n"
                for tag, values in selected
            )
        )

    if args.queue_output:
        args.queue_output.parent.mkdir(parents=True, exist_ok=True)
        lines = []
        for expected_tag, values in selected:
            table = {
                str(pair): value
                for pair, value in zip(TABLE_PAIRS, values, strict=True)
                if value != 0
            }
            line = json.dumps(table, separators=(",", ":"))
            decoded = json.loads(line)
            roundtrip = tuple(int(decoded.get(str(pair), 0)) for pair in TABLE_PAIRS)
            if worker_tag(roundtrip) != expected_tag:
                raise ValueError(f"queue serialization changed tag {expected_tag}")
            lines.append(line)
        args.queue_output.write_text("".join(line + "\n" for line in lines))

    if args.lean_exact_jobs_output:
        args.lean_exact_jobs_output.parent.mkdir(parents=True, exist_ok=True)
        table_dir = args.lean_exact_jobs_output.parent / "tables"
        table_dir.mkdir(parents=True, exist_ok=True)
        jobs = []
        for tag, values in selected:
            table_path = table_dir / f"{tag}.table"
            record = [
                [[pair[0], pair[1]], value]
                for pair, value in zip(TABLE_PAIRS, values, strict=True)
                if value != 0
            ]
            table_path.write_text(json.dumps(record) + "\n")
            jobs.append(
                "\t".join(
                    (tag, str(PROFILE), FAMILY, "MONO", str(table_path), "", "")
                )
            )
        args.lean_exact_jobs_output.write_text("".join(job + "\n" for job in jobs))

    if not args.summary_only:
        print("profile\ttag\ttable_values")
        for tag, values in selected:
            print(f"{PROFILE}\t{tag}\t{' '.join(map(str, values))}")
    print(f"# profile={PROFILE} family={FAMILY} selected={len(selected)}")


if __name__ == "__main__":
    main()
