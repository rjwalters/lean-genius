#!/usr/bin/env python3
"""Fail-closed validation for an H8 slow-unknown follow-up queue."""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
import tempfile
from pathlib import Path

import generate_h8_slow_unknown_followup_queue as queues


HERE = Path(__file__).resolve().parent
MATERIALIZER = HERE / "generate_h7_empty_cube_adaptive_split_jobs.py"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def source_row(source_queue: dict, job: str) -> dict:
    matches = [row for row in source_queue.get("jobs", [])
               if row.get("id") == job]
    require(len(matches) == 1, "source job is not unique in source queue")
    return matches[0]


def validate_bound_queue(queue_path: Path) -> tuple[dict, Path, Path, Path]:
    queue = json.loads(queue_path.read_text())
    require(queue.get("schema") == queues.SCHEMA, "unsupported H8 queue schema")
    require(queue.get("job_count") == 2 and len(queue.get("jobs", [])) == 2,
            "H8 queue must contain exactly two jobs")
    source_queue_path = Path(queue.get("source_queue", ""))
    source_worker = Path(queue.get("source_worker", ""))
    marker = Path(queue.get("source_unknown_marker", ""))
    for path, field in ((source_queue_path, "source_queue_sha256"),
                        (source_worker, "source_worker_sha256"),
                        (marker, "source_unknown_marker_sha256")):
        require(path.is_file() and queues.sha256(path) == queue.get(field),
                f"bound input mismatch: {field}")
    source_queue = json.loads(source_queue_path.read_text())
    row = source_row(source_queue, queue.get("source_job"))
    old_manifest = Path(row.get("manifest", ""))
    require(old_manifest.is_file() and queues.sha256(old_manifest) == row.get("manifest_sha256"),
            "old manifest binding mismatch")
    jobs = queue["jobs"]
    manifests = {Path(job.get("manifest", "")) for job in jobs}
    specs = {Path(job.get("spec", "")) for job in jobs}
    require(len(manifests) == len(specs) == 1,
            "children must share one manifest and spec")
    new_manifest, new_spec = next(iter(manifests)), next(iter(specs))
    require(new_manifest.is_file() and new_spec.is_file(), "new manifest/spec missing")
    expected = queues.build_queue(
        job=queue["source_job"], marker=marker,
        old_manifest=old_manifest, new_manifest=new_manifest, new_spec=new_spec,
        source_queue=source_queue_path, source_worker=source_worker,
        cadical_sha=queue.get("cadical_sha256", ""), cap=queue.get("cap_s"))
    require(queue == expected, "queue differs from authenticated reconstruction")
    return queue, old_manifest, new_manifest, new_spec


def materialize_and_check(queue: dict, new_manifest: Path, new_spec: Path,
                          parent: Path, base: Path) -> list[tuple[str, str]]:
    require(parent.is_file() and base.is_file(), "parent manifest or base CNF missing")
    require(queues.sha256(parent) == queue["parent_manifest_sha256"],
            "parent manifest hash mismatch")
    require(queues.sha256(base) == queue["base_sha256"], "base CNF hash mismatch")
    results = []
    with tempfile.TemporaryDirectory(prefix="erdos85-h8-validate.") as raw:
        root = Path(raw)
        for job in queue["jobs"]:
            output = root / f"{job['id']}.cnf"
            command = [
                sys.executable, str(MATERIALIZER), "materialize",
                "--manifest", str(new_manifest), "--parent-manifest", str(parent),
                "--tree-spec", str(new_spec), "--base", str(base),
                "--leaf", job["id"], "--output", str(output),
            ]
            run = subprocess.run(command, stdout=subprocess.PIPE,
                                 stderr=subprocess.STDOUT, text=True)
            require(run.returncode == 0 and output.is_file(),
                    f"materialization failed for {job['id']}: {run.stdout.strip()}")
            with output.open() as stream:
                header = stream.readline().strip()
            require(header == "p cnf 17633 720829",
                    f"unexpected child CNF shape: {job['id']}")
            digest = queues.sha256(output)
            results.append((job["id"], digest))
    return results


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--queue", type=Path, required=True)
    parser.add_argument("--parent-manifest", type=Path, required=True)
    parser.add_argument("--base", type=Path, required=True)
    parser.add_argument("--materialize", action="store_true")
    args = parser.parse_args()
    queue, _, new_manifest, new_spec = validate_bound_queue(args.queue.resolve())
    suffix = ""
    if args.materialize:
        checked = materialize_and_check(
            queue, new_manifest, new_spec,
            args.parent_manifest.resolve(), args.base.resolve())
        suffix = " " + " ".join(f"{job}_sha256={digest}" for job, digest in checked)
    print(f"H8 FOLLOWUP QUEUE VERIFIED jobs=2 queue_sha256={queues.sha256(args.queue)}" + suffix)


if __name__ == "__main__":
    main()
