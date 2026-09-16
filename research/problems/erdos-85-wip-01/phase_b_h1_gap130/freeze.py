#!/usr/bin/env python3
"""Freeze the 130 capacity gaps outside the Phase B residual H1 queue.

This is a metadata join. It does not materialize CNFs or run solvers.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import sys

BASE = Path(__file__).resolve().parents[1]
OUTPUT = Path(__file__).with_name("gap130.json")
PAIRS = [(a, b) for a in range(8) for b in range(a + 1, 8) if b != (a ^ 1)]


def read(relative: str):
    raw = (BASE / relative).read_bytes()
    return raw, json.loads(raw)


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def tag_of(values: list[int]) -> str:
    assert len(values) == 24 and all(type(v) is int and 0 <= v <= 5 for v in values)
    table = sorted((pair, value) for pair, value in zip(PAIRS, values) if value)
    return hashlib.sha1(json.dumps(table).encode()).hexdigest()[:16]


def freeze() -> dict:
    sources = {}

    def source(relative: str):
        raw, value = read(relative)
        sources[relative] = sha(raw)
        return value

    compact_name = "closure-inventory-evidence/h1-source/capacity-inventory.compact"
    compact = (BASE / compact_name).read_bytes()
    sources[compact_name] = sha(compact)
    capacity = {}
    ordinals = [0] * 5
    for line in compact.decode().splitlines():
        profile, *values = map(int, line.split())
        assert profile in range(5)
        tag = tag_of(values)
        assert tag not in capacity
        capacity[tag] = dict(tag=tag, id="h1_" + tag, profile=profile,
                             capacity_local_index=ordinals[profile], table_values=values)
        ordinals[profile] += 1
    assert ordinals == [1485, 3617, 4717, 2693, 839] and len(capacity) == 13351

    joined = source("closure-inventory-evidence/h1-exact-set-join.json")["rows"]
    assert len(joined) == len(capacity)
    by_tag = {row["tag"]: row for row in joined}
    assert set(by_tag) == set(capacity)
    for tag, row in by_tag.items():
        assert (row["capacity_profile"], row["capacity_local_index"]) == (
            capacity[tag]["profile"], capacity[tag]["capacity_local_index"])
    listed = {row["tag"] for row in joined if row["object_listed"]}
    assert len(listed) == 12054

    rescue = source("closure-inventory-evidence/followup-20260910/h1-rescue-set-join.json")
    rescue_tags = set(rescue["rescue_tags"])
    assert len(rescue_tags) == 13 and len(rescue_tags - listed) == 9
    assert set(rescue["new_to_prior_snapshot"]) == rescue_tags - listed
    gaps = set(capacity) - listed - rescue_tags
    assert len(gaps) == rescue["remaining_metadata_gaps"] == 1288

    frozen = source("phase_b_h1_h3/h1-frozen-candidates.json")["rows"]
    assert len(frozen) == 1257
    frozen_by_id = {row["id"]: row for row in frozen}
    assert len(frozen_by_id) == len(frozen)
    for case_id, row in frozen_by_id.items():
        tag = row["tag"]
        assert case_id == "h1_" + tag and tag in capacity
        assert tag_of(row["table_values"]) == tag
        assert (int(row["profile"]), row["table_values"]) == (
            capacity[tag]["profile"], capacity[tag]["table_values"])

    old = source("phase_b_historical_overlay/historical-95.json")["rows"]
    extra = source("phase_b_historical_overlay_96/historical-96.json")["extra_case"]
    historical = {row["id"]: row for row in old + [extra]}
    assert len(historical) == 96 and set(historical) <= set(frozen_by_id)
    residual = set(frozen_by_id) - set(historical)
    assert len(residual) == 1161
    residual_tags = {case_id[3:] for case_id in residual}
    historical_tags = {case_id[3:] for case_id in historical}
    assert len(residual_tags & gaps) == 1158
    assert len(residual_tags - gaps) == 3
    assert len(historical_tags & gaps) == 96
    outside_frozen = gaps - {row["tag"] for row in frozen}
    assert len(outside_frozen) == 34

    rows = []
    for tag in sorted((historical_tags & gaps) | outside_frozen):
        row = dict(capacity[tag])
        joined_row = by_tag[tag]
        row.update(in_v3_queue=joined_row["in_v3_queue"],
                   claim_recorded=joined_row["claim_recorded"])
        if row["id"] in historical:
            row["class"] = "historical_overlay_without_listed_object"
            row["historical_cnf_sha256"] = historical[row["id"]]["cnf_sha256"]
            assert not row["in_v3_queue"]
        else:
            row["class"] = "outside_frozen_phase_b"
            row["historical_cnf_sha256"] = None
            assert row["in_v3_queue"]
        rows.append(row)
    assert len(rows) == 130
    return {
        "schema": "erdos85-h1-capacity-gap130-v1",
        "scope": "Metadata-only exact complement of the 1161-root Phase B residual dispatch within the dated 1288-gap capacity snapshot; no CNF or verdict claim",
        "source_sha256": sources,
        "capacity_count": 13351,
        "snapshot_object_count_after_rescue": len(listed | rescue_tags),
        "snapshot_gap_count": len(gaps),
        "residual_phase_b_count": len(residual),
        "residual_gap_count": len(residual_tags & gaps),
        "residual_listed_object_count": len(residual_tags - gaps),
        "remaining_gap_count": len(rows),
        "historical_overlay_gap_count": len(historical_tags & gaps),
        "outside_frozen_gap_count": len(outside_frozen),
        "rows": rows,
    }


if __name__ == "__main__":
    raw = (json.dumps(freeze(), indent=2) + "\n").encode()
    if sys.argv[1:] == ["--check"]:
        assert OUTPUT.read_bytes() == raw, "Frozen gap130 manifest changed"
        print("gap130 manifest PASS", sha(raw))
    elif not sys.argv[1:]:
        OUTPUT.write_bytes(raw)
        print("gap130 manifest written", sha(raw))
    else:
        raise SystemExit("usage: freeze.py [--check]")
