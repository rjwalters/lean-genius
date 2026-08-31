#!/usr/bin/env python3
"""Build the exact 406-leaf socket TSV and frozen expectation artifacts."""

from __future__ import annotations

import argparse
import csv
import hashlib
import importlib.util
import json
import os
import re
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent


def load_module(name: str, filename: str):
    spec = importlib.util.spec_from_file_location(name, HERE / filename)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


SOCKETS = load_module("socket_validator", "validate_socket_table.py")
AGGREGATES = load_module("cell_aggregates", "build_small_high_cell_aggregate_receipts.py")
GENERATOR = load_module("cube_module", "generate_small_high_cube_lean_module.py")
SCHEMA = "erdos85-small-high-socket-artifacts-v1"
LEAF_SCHEMA = "erdos85-small-high-leaf-evidence-v1"
REPLAY_SCHEMA = "erdos85-small-high-leaf-replay-v1"
SOURCE_MODULE = "Proofs.Generated.Erdos85OrderFortyNineSmallHighCertificates"
APPROVED_PINS = {
    "root_manifest_sha256": "05381a1cf5e80eb480b6e78c4a8dada2573c1cf2f0c55d9ac0bcc4367e3bca76",
    "queue_receipt_sha256": "fa07876764990816f4d7a5940b09958c33d86676edcc3cddcbabad32b482d103",
    "queue_sha256": "91cd2b14a3d0f5a3b9d30d94a4765928a885da74f428a754aadcda5c9ada504b",
    "worker_receipt_sha256": "35d1f8a4f616630ca60cd37ee364d9bb81080299695f11d0a6fbac11656db108",
    "worker_sha256": "137e57dc3884fc2f61986cb0ed56762e3fe93708331e8f600fc83aa535e5d22a",
}
SHA256 = re.compile(r"[0-9a-f]{64}")
COMMIT = re.compile(r"[0-9a-f]{40}")
LEAF_FIELDS = {"cnf_sha256", "commit", "compact_lrat_sha256", "hypothesis",
    "job_id", "queue_receipt_sha256", "queue_sha256", "replay_receipt_path",
    "replay_receipt_sha256", "review_id", "root_manifest_sha256", "schema",
    "source_module", "theorem", "worker_receipt_sha256", "worker_sha256"}


def canonical(value: object) -> bytes:
    return (json.dumps(value, ensure_ascii=True, allow_nan=False,
                       sort_keys=True, separators=(",", ":")) + "\n").encode("ascii")


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def require_file(path: Path, pin: str, label: str) -> None:
    if not path.is_absolute() or path.is_symlink() or not path.is_file():
        raise ValueError(f"{label} must be an absolute regular non-symlink file")
    if not isinstance(pin, str) or not SHA256.fullmatch(pin) or sha256(path) != pin:
        raise ValueError(f"{label} hash mismatch")


def exact_jobs(manifest: dict) -> list[str]:
    if manifest.get("schema") != "erdos85-small-high-cube-jobs-v1":
        raise ValueError("root manifest schema mismatch")
    cells = manifest.get("cells")
    expected_cells = [cell for _, cell, _ in AGGREGATES.CELLS]
    if not isinstance(cells, dict) or list(cells) != expected_cells:
        raise ValueError("root manifest cell order/set mismatch")
    jobs = []
    for cell in expected_cells:
        actual = [item.get("id") for item in cells[cell].get("jobs", [])]
        expected = AGGREGATES.expected_job_ids(cell)
        if actual != expected:
            raise ValueError(f"{cell}: root manifest job order/set mismatch")
        jobs.extend(actual)
    if len(jobs) != 406 or len(set(jobs)) != 406:
        raise ValueError("root manifest is not the exact 406-job bijection")
    return jobs


def theorem_for(job: str) -> str:
    return f"Erdos85.{GENERATOR.lean_stem(job)}_unsat"


def load_leaf(path: Path, job: str, pins: dict[str, str]) -> dict:
    if not path.is_absolute() or path.is_symlink() or not path.is_file():
        raise ValueError(f"{job}: missing regular non-symlink evidence receipt")
    raw = path.read_bytes()
    leaf = json.loads(raw)
    if not isinstance(leaf, dict) or set(leaf) != LEAF_FIELDS or raw != canonical(leaf):
        raise ValueError(f"{job}: leaf evidence is not exact canonical v1")
    theorem = theorem_for(job)
    fixed = (leaf["schema"], leaf["job_id"], leaf["root_manifest_sha256"],
             leaf["queue_receipt_sha256"], leaf["queue_sha256"],
             leaf["worker_receipt_sha256"], leaf["worker_sha256"],
             leaf["hypothesis"], leaf["theorem"], leaf["source_module"])
    expected = (LEAF_SCHEMA, job, pins["root_manifest_sha256"],
                pins["queue_receipt_sha256"], pins["queue_sha256"],
                pins["worker_receipt_sha256"], pins["worker_sha256"],
                theorem, theorem, SOURCE_MODULE)
    if fixed != expected:
        raise ValueError(f"{job}: leaf lineage/Lean identity mismatch")
    for field in ("cnf_sha256", "compact_lrat_sha256", "replay_receipt_sha256"):
        if not isinstance(leaf[field], str) or not SHA256.fullmatch(leaf[field]):
            raise ValueError(f"{job}: invalid {field}")
    if not COMMIT.fullmatch(str(leaf["commit"])) or not SOCKETS.REVIEW.fullmatch(str(leaf["review_id"])):
        raise ValueError(f"{job}: invalid commit/review identity")
    replay = Path(leaf["replay_receipt_path"])
    require_file(replay, leaf["replay_receipt_sha256"], f"{job} replay receipt")
    replay_value = json.loads(replay.read_text())
    expected_replay = {"cnf_sha256": leaf["cnf_sha256"], "commit": leaf["commit"],
        "compact_lrat_sha256": leaf["compact_lrat_sha256"], "job_id": job,
        "replay_verdict": "VERIFIED", "schema": REPLAY_SCHEMA,
        "source_module": SOURCE_MODULE, "theorem": theorem}
    if replay.read_bytes() != canonical(expected_replay) or replay_value != expected_replay:
        raise ValueError(f"{job}: replay receipt identity mismatch")
    return leaf


def build(root_manifest: Path, pins: dict[str, str], evidence_dir: Path,
          source_commit: str) -> tuple[bytes, bytes, bytes, dict]:
    if set(pins) != {"root_manifest_sha256", "queue_receipt_sha256", "queue_sha256",
                     "worker_receipt_sha256", "worker_sha256"} or any(
            not isinstance(value, str) or not SHA256.fullmatch(value)
            for value in pins.values()):
        raise ValueError("lineage pins must be the exact five SHA-256 fields")
    if pins != APPROVED_PINS:
        raise ValueError("lineage pins differ from the five reviewed production constants")
    require_file(root_manifest, pins["root_manifest_sha256"], "root manifest")
    if not evidence_dir.is_absolute() or evidence_dir.is_symlink() or not evidence_dir.is_dir():
        raise ValueError("evidence directory must be absolute, real, and non-symlink")
    if not COMMIT.fullmatch(source_commit):
        raise ValueError("source commit must be full lowercase hex")
    manifest = json.loads(root_manifest.read_text())
    if root_manifest.read_bytes() != canonical(manifest):
        raise ValueError("root manifest must be canonical JSON")
    jobs = exact_jobs(manifest)
    expected_names = {f"{job}.receipt.json" for job in jobs}
    actual_names = {path.name for path in evidence_dir.iterdir()}
    if actual_names != expected_names:
        raise ValueError("evidence directory must contain exactly 406 receipt files")
    leaves = [load_leaf(evidence_dir / f"{job}.receipt.json", job, pins) for job in jobs]
    if any(leaf["commit"] != source_commit for leaf in leaves):
        raise ValueError("leaf source commits disagree with the pinned commit")
    rows = []
    expected_sockets = []
    for leaf in leaves:
        job = leaf["job_id"]
        row = {"hypothesis": leaf["hypothesis"], "theorem": leaf["theorem"],
            "source_module": leaf["source_module"], "commit": leaf["commit"],
            "campaign_manifest_rows": json.dumps([job], separators=(",", ":")),
            "cnf_sha256": leaf["cnf_sha256"],
            "compact_lrat_sha256": leaf["compact_lrat_sha256"],
            "replay_receipt": leaf["replay_receipt_sha256"],
            "review_id": str(leaf["review_id"])}
        rows.append(row)
        expected_sockets.append({"hypothesis": leaf["hypothesis"],
                                 "campaign_manifest_rows": [job]})
    with tempfile.TemporaryDirectory() as directory:
        table = Path(directory) / "sockets.tsv"
        with table.open("w", newline="") as stream:
            writer = csv.DictWriter(stream, fieldnames=SOCKETS.FIELDS,
                                    delimiter="\t", lineterminator="\n")
            writer.writeheader(); writer.writerows(rows)
        expected_path = Path(directory) / "expected.json"
        expected_path.write_bytes(canonical({"version": 1, "sockets": expected_sockets}))
        if SOCKETS.validate(table, expected_path) != 406:
            raise ValueError("socket validator did not accept exactly 406 rows")
        table_raw, expected_raw = table.read_bytes(), expected_path.read_bytes()
        validation_raw = (SOCKETS.evidence_receipt(table, expected_path, 406) + "\n").encode()
    helpers = [{"source": f"research/problems/erdos-85-wip-01/sat49/{name}",
                "sha256": sha256(HERE / name)} for name in (
                    "validate_socket_table.py",
                    "build_small_high_cell_aggregate_receipts.py",
                    "generate_small_high_cube_lean_module.py")]
    receipt = {"builder_sha256": sha256(Path(__file__)),
        "builder_source": "research/problems/erdos-85-wip-01/sat49/build_small_high_socket_artifacts.py",
        "helper_sources": helpers,
        "evidence_receipts_sha256": hashlib.sha256(canonical([
            sha256(evidence_dir / f"{job}.receipt.json") for job in jobs])).hexdigest(),
        **pins, "schema": SCHEMA, "socket_count": 406,
        "socket_table_sha256": hashlib.sha256(table_raw).hexdigest(),
        "expected_sockets_sha256": hashlib.sha256(expected_raw).hexdigest(),
        "socket_validation_receipt_sha256": hashlib.sha256(validation_raw).hexdigest(),
        "source_commit": source_commit, "source_module": SOURCE_MODULE}
    return table_raw, expected_raw, validation_raw, receipt


def publish(output: Path, artifacts: tuple[bytes, bytes, bytes, dict]) -> None:
    if not output.is_absolute() or output.is_symlink():
        raise ValueError("output must be an absolute absent non-symlink path")
    table, expected, validation, receipt = artifacts
    output.mkdir(parents=False, exist_ok=False)
    for name, raw in (("sockets.tsv", table), ("expected-sockets.json", expected),
                      ("socket-validation.receipt", validation),
                      ("receipt.json", canonical(receipt))):
        path = output / name
        with path.open("xb") as stream:
            stream.write(raw); stream.flush(); os.fsync(stream.fileno())
    descriptor = os.open(output, os.O_RDONLY)
    try: os.fsync(descriptor)
    finally: os.close(descriptor)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root-manifest", type=Path, required=True)
    for name in ("root-manifest", "queue-receipt", "queue", "worker-receipt", "worker"):
        parser.add_argument(f"--{name}-sha256", required=True)
    parser.add_argument("--evidence-dir", type=Path, required=True)
    parser.add_argument("--source-commit", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    pins = {name.replace("-", "_") + "_sha256": getattr(args, name.replace("-", "_") + "_sha256")
            for name in ("root-manifest", "queue-receipt", "queue", "worker-receipt", "worker")}
    artifacts = build(args.root_manifest, pins, args.evidence_dir, args.source_commit)
    publish(args.output, artifacts)
    print(f"WROTE {args.output} sockets=406")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
