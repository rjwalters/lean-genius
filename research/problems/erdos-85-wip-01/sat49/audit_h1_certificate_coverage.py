#!/usr/bin/env python3
"""Audit an h=1 certificate result ledger against the Lean inventory.

Only ``LEAN_ACCEPTED`` rows count as certified.  The script recomputes the
worker's 16-hex orbit tag from every compact inventory row, rejects unknown
or contradictory result rows, and exits nonzero until all 13,541 rows are
accepted.  It deliberately does not infer coverage from the job queue size.
"""

import argparse
import collections
import hashlib
import json
import pathlib
import sys

from enumerate_h1_miss_tables import EDGES


PROFILE_NAMES = ("BBBB", "ABBB", "AABB", "AAAB", "AAAA")
EXPECTED = (1536, 3662, 4801, 2700, 842)
ACCEPTED = "LEAN_ACCEPTED"


def orbit_tag(values):
    items = [
        (edge, value)
        for edge, value in zip(EDGES, values)
        if value
    ]
    return hashlib.sha1(json.dumps(items).encode()).hexdigest()[:16]


def read_inventory(path):
    records = {}
    counts = collections.Counter()
    with path.open(encoding="utf-8") as handle:
        for line_number, line in enumerate(handle, 1):
            fields = line.split()
            if not fields:
                continue
            if len(fields) != 25:
                raise ValueError(
                    f"{path}:{line_number}: expected 25 integers, got {len(fields)}"
                )
            profile, *values = map(int, fields)
            if not 0 <= profile < 5:
                raise ValueError(f"{path}:{line_number}: invalid profile {profile}")
            if any(not 0 <= value < 5 for value in values):
                raise ValueError(f"{path}:{line_number}: value outside [0,4]")
            tag = orbit_tag(values)
            old = records.get(tag)
            record = (profile, tuple(values), line_number)
            if old is not None:
                raise ValueError(
                    f"{path}:{line_number}: duplicate/colliding tag {tag}; "
                    f"first seen on line {old[2]}"
                )
            records[tag] = record
            counts[profile] += 1
    actual = tuple(counts[index] for index in range(5))
    if actual != EXPECTED:
        raise ValueError(f"inventory profile counts {actual}, expected {EXPECTED}")
    return records


def read_results(path, inventory):
    statuses = {}
    with path.open(encoding="utf-8") as handle:
        for line_number, line in enumerate(handle, 1):
            fields = line.rstrip("\n").split("\t")
            if not fields or not fields[0]:
                continue
            if len(fields) < 2:
                raise ValueError(f"{path}:{line_number}: malformed result row")
            tag, status = fields[:2]
            if tag not in inventory:
                raise ValueError(f"{path}:{line_number}: unknown orbit tag {tag}")
            old = statuses.get(tag)
            if old is not None and old != status:
                raise ValueError(
                    f"{path}:{line_number}: conflicting statuses for {tag}: "
                    f"{old} versus {status}"
                )
            statuses[tag] = status
    return statuses


def report(inventory, statuses):
    accepted = collections.Counter()
    failed = collections.Counter()
    pending = collections.Counter()
    for tag, (profile, _values, _line) in inventory.items():
        status = statuses.get(tag)
        if status == ACCEPTED:
            accepted[profile] += 1
        elif status is None:
            pending[profile] += 1
        else:
            failed[profile] += 1
    for profile, name in enumerate(PROFILE_NAMES):
        print(
            f"{name}\taccepted={accepted[profile]}\tfailed={failed[profile]}"
            f"\tpending={pending[profile]}\ttotal={EXPECTED[profile]}"
        )
    accepted_total = sum(accepted.values())
    failed_total = sum(failed.values())
    pending_total = sum(pending.values())
    print(
        f"TOTAL\taccepted={accepted_total}\tfailed={failed_total}"
        f"\tpending={pending_total}\ttotal={sum(EXPECTED)}"
    )
    return accepted_total == sum(EXPECTED)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("inventory", type=pathlib.Path)
    parser.add_argument("results", type=pathlib.Path)
    args = parser.parse_args()
    try:
        inventory = read_inventory(args.inventory)
        statuses = read_results(args.results, inventory)
        complete = report(inventory, statuses)
    except (OSError, ValueError) as error:
        print(f"coverage audit failed: {error}", file=sys.stderr)
        return 2
    return 0 if complete else 1


if __name__ == "__main__":
    sys.exit(main())
