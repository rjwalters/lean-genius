#!/usr/bin/env python3
"""Audit/export the 190 h=1 orbit rows removed by cross-miss capacity.

The predicate exactly mirrors ``oneHighTableCrossMissCapacity`` in
``Erdos85OneHighV2CapacityInventory.lean``.  By default the script prints one
TSV row per removed orbit.  If a results ledger is supplied, it also reports
whether the latest status is ``LEAN_ACCEPTED``.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from collections import Counter
from pathlib import Path


MATE = (1, 0, 3, 2, 5, 4, 7, 6)
TABLE_PAIRS = tuple(
    (left, right)
    for left in range(8)
    for right in range(left + 1, 8)
    if MATE[left] != right
)
EXPECTED_TOTALS = (1536, 3662, 4801, 2700, 842)
EXPECTED_RETAINED = (1485, 3617, 4717, 2693, 839)


def worker_tag(values: tuple[int, ...]) -> str:
    table = {
        pair: value
        for pair, value in zip(TABLE_PAIRS, values, strict=True)
        if value != 0
    }
    payload = json.dumps(sorted(table.items())).encode()
    return hashlib.sha1(payload).hexdigest()[:16]


def has_cross_miss_capacity(values: tuple[int, ...]) -> bool:
    table = [[0] * 8 for _ in range(8)]
    for (left, right), value in zip(TABLE_PAIRS, values, strict=True):
        table[left][right] = value
        table[right][left] = value
    return all(
        table[left][MATE[right]] + table[right][MATE[left]] <= 5
        for left, right in TABLE_PAIRS
    )


def read_latest_results(path: Path | None) -> dict[str, str]:
    latest: dict[str, str] = {}
    if path is None:
        return latest
    for line_number, raw in enumerate(path.read_text().splitlines(), 1):
        fields = raw.split("\t")
        if len(fields) < 2:
            raise ValueError(f"{path}:{line_number}: malformed result row")
        latest[fields[0]] = fields[1]
    return latest


def main() -> None:
    script = Path(__file__).resolve()
    repo = script.parents[4]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--inventory",
        type=Path,
        default=repo / "proofs/Proofs/Certificates/h1_orbit_inventory.compact",
    )
    parser.add_argument("--results", type=Path)
    parser.add_argument(
        "--retained-output",
        type=Path,
        help=(
            "atomically write the authoritative 13,351-row capacity compact "
            "inventory in Lean filter order"
        ),
    )
    parser.add_argument(
        "--summary-only",
        action="store_true",
        help="suppress the removed-tag TSV rows",
    )
    args = parser.parse_args()
    latest = read_latest_results(args.results)

    totals = Counter()
    retained = Counter()
    retained_lines: list[str] = []
    removed: list[tuple[int, str, str]] = []
    for line_number, raw in enumerate(args.inventory.read_text().splitlines(), 1):
        fields = raw.split()
        if not fields:
            continue
        profile, *raw_values = map(int, fields)
        values = tuple(raw_values)
        if profile not in range(5) or len(values) != len(TABLE_PAIRS):
            raise ValueError(f"{args.inventory}:{line_number}: malformed inventory row")
        tag = worker_tag(values)
        totals[profile] += 1
        if has_cross_miss_capacity(values):
            retained[profile] += 1
            retained_lines.append(raw + "\n")
        else:
            removed.append((profile, tag, latest.get(tag, "MISSING")))

    actual_totals = tuple(totals[index] for index in range(5))
    actual_retained = tuple(retained[index] for index in range(5))
    if actual_totals != EXPECTED_TOTALS:
        raise ValueError(f"unexpected totals: {actual_totals}")
    if actual_retained != EXPECTED_RETAINED:
        raise ValueError(f"unexpected retained counts: {actual_retained}")
    if len(removed) != 190:
        raise ValueError(f"expected 190 removed rows, found {len(removed)}")

    if args.retained_output:
        args.retained_output.parent.mkdir(parents=True, exist_ok=True)
        temporary = args.retained_output.with_name(
            f".{args.retained_output.name}.tmp.{os.getpid()}"
        )
        try:
            temporary.write_text("".join(retained_lines))
            os.replace(temporary, args.retained_output)
        finally:
            if temporary.exists():
                temporary.unlink()

    if not args.summary_only:
        print("profile\ttag\tlatest_status")
        for profile, tag, status in removed:
            print(f"{profile}\t{tag}\t{status}")
    accepted = sum(status == "LEAN_ACCEPTED" for _, _, status in removed)
    print(
        f"# total=13541 retained=13351 removed=190 "
        f"removed_accepted={accepted} removed_not_accepted={190 - accepted}"
    )


if __name__ == "__main__":
    main()
