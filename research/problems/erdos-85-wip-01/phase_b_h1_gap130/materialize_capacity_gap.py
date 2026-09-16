#!/usr/bin/env python3
"""Materialize one of the 34 H1 capacity gaps absent from Phase B.

The command only emits and checks a CNF. It never starts a SAT solver.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
SAT49 = HERE.parent / "sat49"
sys.path.insert(0, str(SAT49))

import materialize_h1_verdict_input as native  # noqa: E402
from freeze import freeze, tag_of  # noqa: E402

MANIFEST = HERE / "gap130.json"
MANIFEST_SHA256 = "e65684212b851d3fa3cb0e7598b6ead5662da7b3abcc97c64835945cccd7baf0"
NATIVE_SHA256 = "00201aa9e23c2c55bce8cab3532d5eaf34df9fdb24d0134df01a974e0ff74dbd"


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def select(case_id: str) -> dict:
    if native.sha256(Path(native.__file__)) != NATIVE_SHA256:
        raise ValueError("Reviewed native H1 materializer changed")
    raw = MANIFEST.read_bytes()
    if sha(raw) != MANIFEST_SHA256:
        raise ValueError("Gap130 manifest bytes changed")
    manifest = json.loads(raw)
    if manifest != freeze():
        raise ValueError("Gap130 source snapshot or derived join changed")
    rows = [row for row in manifest["rows"] if row["id"] == case_id]
    if len(rows) != 1 or rows[0]["class"] != "outside_frozen_phase_b":
        raise ValueError("Case is absent from the 34 outside-frozen gaps")
    row = rows[0]
    if (row["id"] != "h1_" + row["tag"] or
            tag_of(row["table_values"]) != row["tag"] or
            not row["in_v3_queue"] or row["historical_cnf_sha256"] is not None):
        raise ValueError("Capacity-table identity mismatch")
    return row


def one_row_manifest(row: dict) -> bytes:
    """Build the exact input format of the reviewed native H1 materializer."""
    candidate = {
        "id": row["id"],
        "tag": row["tag"],
        "profile": str(row["profile"]),
        "table_values": row["table_values"],
        "host_cnf_sha256": "",
        "fleet_cnf_sha256": "",
        "fleet_v2_cnf_sha256": "",
        "fleet_v3_cnf_sha256": "",
    }
    return (json.dumps({"schema": "erdos85-phase-b-h1-candidates-v1",
                        "rows": [candidate]}, indent=2) + "\n").encode()


def materialize(case_id: str, output_dir: Path) -> dict:
    row = select(case_id)
    output_dir = output_dir.resolve()
    output_dir.mkdir()  # Exclusive; never reuse an old receipt or input.
    adapter = one_row_manifest(row)
    adapter_path = output_dir / "one-row-source.json"
    adapter_path.write_bytes(adapter)
    adapter_sha = sha(adapter)
    record = {
        "schema": "erdos85-h1-capacity-gap-native-binding-v1",
        "status": "ERROR",
        "id": case_id,
        "tag": row["tag"],
        "profile": row["profile"],
        "capacity_local_index": row["capacity_local_index"],
        "gap130_sha256": MANIFEST_SHA256,
        "one_row_source_sha256": adapter_sha,
        "native_materializer_sha256": NATIVE_SHA256,
        "solver_launched": False,
    }
    try:
        result = native.materialize(adapter_path, adapter_sha, case_id,
                                    output_dir / "native")
        if (result["id"] != case_id or result["tag"] != row["tag"] or
                result["profile"] != row["profile"] or
                result["manifest_sha256"] != adapter_sha or
                result["status"] != "materialized" or
                result["solver_launched"] is not False):
            raise ValueError("Native receipt does not bind the selected capacity row")
        record.update(status="materialized", cnf_sha256=result["cnf_sha256"],
                      cnf_bytes=result["cnf_bytes"],
                      native_receipt_sha256=native.sha256(output_dir / "native/receipt.json"))
    except BaseException as error:
        record["error"] = f"{type(error).__name__}: {error}"
        raise
    finally:
        (output_dir / "binding.json").write_text(json.dumps(record, indent=2) + "\n")
    return record


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case-id", required=True)
    parser.add_argument("--execute", action="store_true")
    parser.add_argument("--output-dir", type=Path)
    args = parser.parse_args()
    row = select(args.case_id)
    if not args.execute:
        print(json.dumps({"mode": "dry_run", "id": row["id"],
                          "profile": row["profile"],
                          "capacity_local_index": row["capacity_local_index"],
                          "tag": row["tag"], "one_row_source_sha256":
                          sha(one_row_manifest(row)), "solver_launched": False}))
        return 0
    if args.output_dir is None:
        parser.error("--execute requires a new --output-dir")
    print(json.dumps(materialize(args.case_id, args.output_dir)))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
