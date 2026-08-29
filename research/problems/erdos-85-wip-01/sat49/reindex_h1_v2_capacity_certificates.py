#!/usr/bin/env python3
"""Re-key tag-addressed H1 certificate indexes to Lean capacity ordinals.

Solver queues may use raw-inventory or family-local indexes.  Those operational
indexes are not Lean identities.  This tool reconstructs the unique
``(profile, localIndex)`` of every certificate from the authoritative ordered
capacity inventory, then emits the exact TSV contract consumed by the H1 leaf
and aggregate generators.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import replace
from pathlib import Path

from generate_h1_v2_lean_aggregate import read_capacity_inventory
from generate_h1_v2_lean_stubs import (
    CAPACITY_PROFILE_COUNTS,
    EXPECTED_COLUMNS,
    IndexRow,
    atomic_write,
    read_index,
    sha256,
)


def capacity_key_map(inventory: Path) -> dict[str, tuple[int, int]]:
    profiles = read_capacity_inventory(inventory)
    return {
        tag: (profile, local_index)
        for profile, tags in enumerate(profiles)
        for local_index, tag in enumerate(tags)
    }


def reindex_rows(
    indexes: list[Path], capacity_keys: dict[str, tuple[int, int]],
    drop_outside_capacity: bool = False, require_complete: bool = False,
) -> list[IndexRow]:
    by_tag: dict[str, IndexRow] = {}
    seen_tags: set[str] = set()
    outside: list[str] = []
    for path in indexes:
        for row in read_index(path):
            if row.orbit in seen_tags:
                raise ValueError(f"duplicate certificate orbit across indexes: {row.orbit}")
            seen_tags.add(row.orbit)
            key = capacity_keys.get(row.orbit)
            if key is None:
                outside.append(row.orbit)
                continue
            profile, local_index = key
            if row.profile != profile:
                raise ValueError(
                    f"{row.orbit}: certificate profile {row.profile} disagrees "
                    f"with capacity profile {profile}"
                )
            by_tag[row.orbit] = replace(row, local_index=local_index)
    if outside and not drop_outside_capacity:
        raise ValueError(
            f"{len(outside)} certificate orbit(s) are outside the capacity inventory; "
            "use --drop-outside-capacity only for audited historical inputs"
        )
    if require_complete:
        missing = capacity_keys.keys() - by_tag.keys()
        if missing:
            raise ValueError(
                f"capacity certificate index is incomplete: {len(missing)} missing row(s)"
            )
    return sorted(by_tag.values(), key=lambda row: (row.profile, row.local_index))


def row_fields(row: IndexRow) -> list[str]:
    values = {
        "orbit": row.orbit,
        "profile": ("BBBB", "ABBB", "AABB", "AAAB", "AAAA")[row.profile],
        "localIndex": str(row.local_index),
        "compact_lrat_sha256": row.compact_sha,
        "raw_lrat_sha256": row.raw_sha,
        "cnf_sha256": row.cnf_sha,
        "lrat_actions": "" if row.actions is None else str(row.actions),
        "source_cnf_clauses": str(row.clauses),
        "compact_bytes": str(row.compact_bytes),
        "stub_ready": "1" if row.stub_ready else "0",
        "binary_lrat_sha256": row.binary_sha,
        "binary_bytes": str(row.binary_bytes),
        "lz4_frame_sha256": row.frame_sha,
        "lz4_frame_bytes": str(row.frame_bytes),
        "packed_lz4_sha256": row.packed_sha,
        "packed_lz4_bytes": str(row.packed_bytes),
    }
    return [values[column] for column in EXPECTED_COLUMNS]


def render_index(rows: list[IndexRow]) -> str:
    lines = ["\t".join(EXPECTED_COLUMNS)]
    lines.extend("\t".join(row_fields(row)) for row in rows)
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--inventory", type=Path, required=True)
    parser.add_argument("--index", type=Path, action="append", required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument(
        "--receipt-output", type=Path,
        help="atomically record the input/output hashes and exact dropped-tag set",
    )
    parser.add_argument("--drop-outside-capacity", action="store_true")
    parser.add_argument("--require-complete", action="store_true")
    args = parser.parse_args()
    keys = capacity_key_map(args.inventory)
    if len(keys) != sum(CAPACITY_PROFILE_COUNTS):
        raise ValueError("capacity inventory contains duplicate orbit tags")
    rows = reindex_rows(
        args.index, keys, args.drop_outside_capacity, args.require_complete
    )
    atomic_write(args.output, render_index(rows))
    if args.receipt_output:
        emitted_tags = {row.orbit for row in rows}
        input_tags = {
            row.orbit
            for path in args.index
            for row in read_index(path)
        }
        receipt = {
            "schema": "erdos85-h1-v2-capacity-reindex-v1",
            "inventory": str(args.inventory.resolve()),
            "inventory_sha256": sha256(args.inventory),
            "indexes": [
                {"path": str(path.resolve()), "sha256": sha256(path)}
                for path in args.index
            ],
            "output": str(args.output.resolve()),
            "output_sha256": sha256(args.output),
            "capacity_total": len(keys),
            "emitted_rows": len(rows),
            "dropped_outside_capacity_tags": sorted(input_tags - emitted_tags),
            "require_complete": args.require_complete,
        }
        atomic_write(
            args.receipt_output,
            json.dumps(receipt, indent=2, sort_keys=True) + "\n",
        )
    print(f"rows={len(rows)} capacity_total={len(keys)} output={args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
