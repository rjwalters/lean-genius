#!/usr/bin/env python3
"""Validate replay queue identities against a receipted capacity index."""

from __future__ import annotations

import csv
import hashlib
import json
from pathlib import Path
from typing import Any

from replay_common import ReplayError, load_json, require_sha, require_tag, sha256_file


PROFILE_NAMES = ("BBBB", "ABBB", "AABB", "AAAB", "AAAA")
CAPACITY_PROFILE_COUNTS = (1485, 3617, 4717, 2693, 839)
MATE = (1, 0, 3, 2, 5, 4, 7, 6)
TABLE_PAIRS = tuple(
    (left, right)
    for left in range(8)
    for right in range(left + 1, 8)
    if MATE[left] != right
)


def load_capacity_index(path: Path) -> dict[str, tuple[int, int]]:
    result: dict[str, tuple[int, int]] = {}
    slots: set[tuple[int, int]] = set()
    with path.open(newline="") as stream:
        reader = csv.DictReader(stream, delimiter="\t")
        required = {"orbit", "profile", "localIndex"}
        if not reader.fieldnames or not required.issubset(reader.fieldnames):
            raise ReplayError(f"{path}: capacity index lacks {sorted(required)}")
        for line_number, row in enumerate(reader, 2):
            try:
                tag = require_tag(row["orbit"])
                profile = PROFILE_NAMES.index(row["profile"])
                local_index = int(row["localIndex"])
            except (ReplayError, ValueError) as error:
                raise ReplayError(f"{path}:{line_number}: malformed capacity key") from error
            if local_index < 0:
                raise ReplayError(f"{path}:{line_number}: negative capacity ordinal")
            slot = (profile, local_index)
            if tag in result or slot in slots:
                raise ReplayError(f"{path}:{line_number}: duplicate capacity tag or slot")
            result[tag] = slot
            slots.add(slot)
    if not result:
        raise ReplayError("capacity index is empty")
    return result


def validate_reindex_receipt(
    path: Path, capacity_index: Path, inventory_sha256: str,
) -> dict[str, Any]:
    receipt = load_json(path)
    if receipt.get("schema") != "erdos85-h1-v2-capacity-reindex-v1":
        raise ReplayError("capacity reindex receipt has wrong schema")
    if receipt.get("inventory_sha256") != require_sha(
        inventory_sha256, "manifest.inventory_sha256"
    ):
        raise ReplayError("capacity reindex receipt inventory hash mismatch")
    if receipt.get("output_sha256") != sha256_file(capacity_index):
        raise ReplayError("capacity reindex receipt output hash mismatch")
    emitted = receipt.get("emitted_rows")
    if type(emitted) is not int or emitted <= 0:
        raise ReplayError("capacity reindex receipt emitted_rows is invalid")
    return receipt


def validate_queue_capacity(
    jobs: list[dict[str, Any]], capacity: dict[str, tuple[int, int]],
    require_complete: bool,
) -> None:
    for job in jobs:
        expected = capacity.get(job["tag"])
        actual = (job["profile"], job["local_index"])
        if expected is None:
            raise ReplayError(f"queue tag is absent from capacity index: {job['tag']}")
        if actual != expected:
            raise ReplayError(
                f"queue tag {job['tag']} uses slot {actual}, expected capacity slot {expected}"
            )
    if require_complete:
        expected_total = sum(CAPACITY_PROFILE_COUNTS)
        if len(capacity) != expected_total:
            raise ReplayError(
                f"complete capacity index must have {expected_total} rows, found {len(capacity)}"
            )
        expected_slots = {
            (profile, local_index)
            for profile, count in enumerate(CAPACITY_PROFILE_COUNTS)
            for local_index in range(count)
        }
        if set(capacity.values()) != expected_slots:
            raise ReplayError("capacity index does not exactly enumerate all capacity ordinals")
        if {job["tag"] for job in jobs} != set(capacity):
            raise ReplayError("complete replay queue does not exactly cover the capacity index")


def table_serialization_tag(serialization: str) -> str:
    try:
        records = json.loads(serialization)
    except json.JSONDecodeError as error:
        raise ReplayError("job table_serialization is not JSON") from error
    if not isinstance(records, list):
        raise ReplayError("job table_serialization must be a JSON list")
    table: dict[tuple[int, int], int] = {}
    for record in records:
        if (
            not isinstance(record, list) or len(record) != 2
            or not isinstance(record[0], list) or len(record[0]) != 2
            or any(type(endpoint) is not int for endpoint in record[0])
            or type(record[1]) is not int or record[1] <= 0
        ):
            raise ReplayError("job table_serialization has a malformed table entry")
        pair = tuple(record[0])
        if pair not in TABLE_PAIRS or pair in table:
            raise ReplayError("job table_serialization has an invalid or duplicate pair")
        table[pair] = record[1]
    payload = json.dumps(sorted(table.items())).encode()
    return hashlib.sha1(payload).hexdigest()[:16]


def validate_queue_tables(jobs: list[dict[str, Any]]) -> None:
    for job in jobs:
        if table_serialization_tag(job["table_serialization"]) != job["tag"]:
            raise ReplayError(
                f"queue table serialization does not hash to tag {job['tag']}"
            )
