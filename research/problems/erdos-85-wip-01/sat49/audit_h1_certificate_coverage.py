#!/usr/bin/env python3
"""Audit exact-v2 h=1 certificate coverage against the Lean inventory.

The inventory is the same compact artifact consumed by
``Erdos85OneHighV2Inventory.lean``.  A result counts as accepted only when
its latest ledger row is ``LEAN_ACCEPTED``; solver verdicts are deliberately
not treated as certificates.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
from collections import Counter
from dataclasses import dataclass
from pathlib import Path


PROFILE_NAMES = ("BBBB", "ABBB", "AABB", "AAAB", "AAAA")
TABLE_PAIRS = tuple(
    (c, j)
    for c in range(8)
    for j in range(c + 1, 8)
    if j != (c ^ 1)
)
assert len(TABLE_PAIRS) == 24


@dataclass(frozen=True)
class InventoryEntry:
    profile: int
    values: tuple[int, ...]
    tag: str


def worker_tag(values: tuple[int, ...]) -> str:
    """Reproduce the tag computation in sweep_worker.py exactly."""
    table = {
        pair: value
        for pair, value in zip(TABLE_PAIRS, values, strict=True)
        if value != 0
    }
    payload = json.dumps(sorted(table.items())).encode()
    return hashlib.sha1(payload).hexdigest()[:16]


def read_inventory(path: Path) -> list[InventoryEntry]:
    entries: list[InventoryEntry] = []
    for line_number, raw in enumerate(path.read_text().splitlines(), 1):
        fields = raw.split()
        if not fields:
            continue
        try:
            profile, *values = map(int, fields)
        except ValueError as error:
            raise ValueError(f"{path}:{line_number}: non-integer field") from error
        if profile not in range(5):
            raise ValueError(f"{path}:{line_number}: profile {profile} is not in [0, 5)")
        if len(values) != len(TABLE_PAIRS):
            raise ValueError(
                f"{path}:{line_number}: expected 24 values, found {len(values)}"
            )
        if any(value not in range(5) for value in values):
            raise ValueError(f"{path}:{line_number}: table value is not in [0, 5)")
        value_tuple = tuple(values)
        entries.append(InventoryEntry(profile, value_tuple, worker_tag(value_tuple)))

    tags = [entry.tag for entry in entries]
    if len(tags) != len(set(tags)):
        duplicates = sorted(tag for tag, count in Counter(tags).items() if count > 1)
        raise ValueError(f"inventory worker tags are not unique: {duplicates[:5]}")
    return entries


def read_latest_results(path: Path) -> dict[str, str]:
    latest: dict[str, str] = {}
    if not path.exists():
        return latest
    for line_number, raw in enumerate(path.read_text().splitlines(), 1):
        if not raw:
            continue
        fields = raw.split("\t")
        if len(fields) < 2:
            raise ValueError(f"{path}:{line_number}: expected tab-separated tag and state")
        latest[fields[0]] = fields[1].strip()
    return latest


def read_stub_ready_index(path: Path) -> set[str]:
    """Read the cert-root v2 index, rejecting pre-v2/raw-only schemas."""
    required = {"orbit", "profile", "localIndex", "compact_lrat_sha256", "stub_ready"}
    ready: set[str] = set()
    seen: set[str] = set()
    with path.open(newline="") as stream:
        reader = csv.DictReader(stream, delimiter="\t")
        fields = set(reader.fieldnames or ())
        if not required <= fields:
            raise ValueError(f"{path}: not a cert-root v2 index; missing {required - fields}")
        for line_number, row in enumerate(reader, 2):
            tag = row["orbit"]
            if tag in seen:
                raise ValueError(f"{path}:{line_number}: duplicate orbit {tag}")
            seen.add(tag)
            state = row["stub_ready"]
            if state not in ("0", "1"):
                raise ValueError(f"{path}:{line_number}: stub_ready must be 0 or 1")
            if state == "1":
                ready.add(tag)
    return ready


def audit(
    entries: list[InventoryEntry], latest: dict[str, str], stub_ready: set[str]
) -> tuple[list[Counter], set[str], set[str]]:
    inventory_tags = {entry.tag for entry in entries}
    rows = [Counter() for _ in PROFILE_NAMES]
    for entry in entries:
        state = latest.get(entry.tag)
        if state == "LEAN_ACCEPTED":
            bucket = "accepted"
        elif state is None:
            bucket = "pending"
        else:
            bucket = "failed"
        rows[entry.profile][bucket] += 1
        if entry.tag in stub_ready:
            rows[entry.profile]["stub_ready"] += 1
        rows[entry.profile]["total"] += 1
    return rows, set(latest) - inventory_tags, stub_ready - inventory_tags


def main() -> int:
    script = Path(__file__).resolve()
    default_inventory = (
        script.parents[4]
        / "proofs/Proofs/Certificates/h1_orbit_inventory.compact"
    )
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--inventory", type=Path, default=default_inventory)
    parser.add_argument("--results", type=Path, required=True)
    parser.add_argument(
        "--cert-index",
        type=Path,
        help="cert-root v2 index; when supplied, completion requires stub_ready coverage",
    )
    parser.add_argument(
        "--require-complete",
        action="store_true",
        help="exit nonzero unless every inventory row is LEAN_ACCEPTED",
    )
    args = parser.parse_args()

    entries = read_inventory(args.inventory)
    if len(entries) != 13_541:
        raise ValueError(f"expected 13541 inventory rows, found {len(entries)}")
    latest = read_latest_results(args.results)
    stub_ready = read_stub_ready_index(args.cert_index) if args.cert_index else set()
    rows, unknown, unknown_stubs = audit(entries, latest, stub_ready)

    total = Counter()
    for name, row in zip(PROFILE_NAMES, rows, strict=True):
        total.update(row)
        print(
            f"{name:4}  stub_ready={row['stub_ready']:5}  "
            f"accepted={row['accepted']:5}  failed={row['failed']:5}  "
            f"pending={row['pending']:5}  total={row['total']:5}"
        )
    print(
        f"TOTAL stub_ready={total['stub_ready']:5}  accepted={total['accepted']:5}  "
        f"failed={total['failed']:5}  "
        f"pending={total['pending']:5}  total={total['total']:5}"
    )
    if unknown:
        print(f"WARNING ledger has {len(unknown)} tag(s) absent from inventory")
    if unknown_stubs:
        print(f"WARNING cert index has {len(unknown_stubs)} tag(s) absent from inventory")

    covered = total["stub_ready"] if args.cert_index else total["accepted"]
    complete = covered == total["total"] and not unknown and not unknown_stubs
    return 0 if complete or not args.require_complete else 1


if __name__ == "__main__":
    raise SystemExit(main())
