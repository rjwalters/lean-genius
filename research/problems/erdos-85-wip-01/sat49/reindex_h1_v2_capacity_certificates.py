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
    return reindex_loaded_rows(
        [read_index(path) for path in indexes], capacity_keys,
        drop_outside_capacity, require_complete,
    )


def reindex_loaded_rows(
    indexes: list[list[IndexRow]], capacity_keys: dict[str, tuple[int, int]],
    drop_outside_capacity: bool = False, require_complete: bool = False,
) -> list[IndexRow]:
    by_tag: dict[str, IndexRow] = {}
    seen_tags: set[str] = set()
    outside: list[str] = []
    for index in indexes:
        for row in index:
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


def require_unchanged(paths: list[Path], expected_hashes: list[str]) -> None:
    if len(paths) != len(expected_hashes):
        raise ValueError("internal input/hash cardinality mismatch")
    changed = [
        str(path.resolve())
        for path, expected in zip(paths, expected_hashes, strict=True)
        if sha256(path) != expected
    ]
    if changed:
        raise ValueError(f"reindex input changed during freeze: {changed}")


def require_distinct_paths(
    inputs: list[Path], output: Path, receipt_output: Path | None,
) -> None:
    labeled = [("input", path.resolve()) for path in inputs]
    labeled.append(("output", output.resolve()))
    if receipt_output is not None:
        labeled.append(("receipt output", receipt_output.resolve()))
    seen: dict[Path, str] = {}
    for label, path in labeled:
        previous = seen.get(path)
        if previous is not None:
            raise ValueError(f"reindex paths alias: {previous} and {label}: {path}")
        seen[path] = label


def require_fresh_outputs(output: Path, receipt_output: Path | None) -> None:
    for label, path in (("output", output), ("receipt output", receipt_output)):
        if path is not None and (path.exists() or path.is_symlink()):
            raise ValueError(f"reindex {label} must not already exist: {path.resolve()}")


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
    inputs = [args.inventory, *args.index]
    require_distinct_paths(inputs, args.output, args.receipt_output)
    require_fresh_outputs(args.output, args.receipt_output)
    input_hashes = [sha256(path) for path in inputs]
    keys = capacity_key_map(args.inventory)
    if len(keys) != sum(CAPACITY_PROFILE_COUNTS):
        raise ValueError("capacity inventory contains duplicate orbit tags")
    loaded_indexes = [read_index(path) for path in args.index]
    # These hashes bind the bytes just parsed, rather than a later reread that
    # may have raced an external ledger/index update.
    require_unchanged(inputs, input_hashes)
    rows = reindex_loaded_rows(
        loaded_indexes, keys, args.drop_outside_capacity, args.require_complete
    )
    atomic_write(args.output, render_index(rows))
    # Refuse a successful freeze if an input changed while output was emitted.
    require_unchanged(inputs, input_hashes)
    if args.receipt_output:
        emitted_tags = {row.orbit for row in rows}
        input_tags = {
            row.orbit
            for index in loaded_indexes
            for row in index
        }
        receipt = {
            "schema": "erdos85-h1-v2-capacity-reindex-v1",
            "inventory": str(args.inventory.resolve()),
            "inventory_sha256": input_hashes[0],
            "indexes": [
                {"path": str(path.resolve()), "sha256": digest}
                for path, digest in zip(
                    args.index, input_hashes[1:], strict=True
                )
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
