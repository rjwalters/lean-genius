#!/usr/bin/env python3
"""Dispatch a manifest-bound H1 replay queue on one dedicated node.

The initial production benchmark is deliberately single-node and P=1.  This
dispatcher may raise local concurrency after the measured benchmark.  Goal #44
selected a manifest-bound host-local lock rather than distributed leasing;
another dispatcher fails before scheduling even with a different state dir.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import fcntl
import json
import os
import subprocess
import sys
import time
from pathlib import Path
from typing import Any

from replay_common import ReplayError, atomic_write, canonical_json, load_manifest, require_tag, sha256_file
from replay_worker import validate_job


HERE = Path(__file__).resolve().parent
WORKER = HERE / "replay_worker.py"


def acquire_single_writer_lock(lock_path: Path):
    """Hold a host-local exclusive lock for the complete dispatcher lifetime."""
    lock_path = lock_path.resolve()
    lock_path.parent.mkdir(parents=True, exist_ok=True)
    handle = lock_path.open("a+", encoding="utf-8")
    try:
        fcntl.flock(handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError as error:
        handle.close()
        raise ReplayError("another replay dispatcher holds the single-writer lock") from error
    handle.seek(0)
    handle.truncate()
    handle.write(json.dumps({"pid": os.getpid(), "acquired_unix_ns": time.time_ns()}, sort_keys=True) + "\n")
    handle.flush()
    os.fsync(handle.fileno())
    return handle


def load_queue(path: Path) -> list[dict[str, Any]]:
    jobs: list[dict[str, Any]] = []
    for line_number, line in enumerate(path.read_text().splitlines(), 1):
        if not line:
            continue
        try:
            job = json.loads(line)
        except json.JSONDecodeError as error:
            raise ReplayError(f"{path}:{line_number}: malformed JSON") from error
        if not isinstance(job, dict):
            raise ReplayError(f"{path}:{line_number}: job must be an object")
        tag = require_tag(job.get("tag"))
        try:
            jobs.append(validate_job(job, tag))
        except ReplayError as error:
            raise ReplayError(f"{path}:{line_number}: {error}") from error
    tags = [job["tag"] for job in jobs]
    if len(tags) != len(set(tags)):
        raise ReplayError("queue contains duplicate tags")
    if tags != sorted(tags):
        raise ReplayError("queue must be sorted by tag")
    slots = [(job["profile"], job["local_index"]) for job in jobs]
    if len(slots) != len(set(slots)):
        raise ReplayError("queue contains duplicate profile/local-index slots")
    if not jobs:
        raise ReplayError("queue is empty")
    return jobs


def run_job(args: argparse.Namespace, job: dict[str, Any], queue_sha: str,
            worker_sha: str) -> dict[str, Any]:
    tag = job["tag"]
    job_dir = args.state_dir / "jobs"
    job_dir.mkdir(parents=True, exist_ok=True)
    job_path = job_dir / f"{tag}.json"
    atomic_write(job_path, canonical_json(job))
    command = [
        sys.executable, str(WORKER), "--manifest", str(args.manifest),
        "--job", str(job_path), "--tag", tag, "--state-dir", str(args.state_dir),
    ]
    if args.object_store_root is not None:
        command.extend(["--object-store-root", str(args.object_store_root)])
    else:
        command.extend(["--s3-bucket", args.s3_bucket, "--aws", args.aws])
    started = time.time_ns()
    completed = subprocess.run(command, text=True, capture_output=True, check=False)
    finished = time.time_ns()
    receipt = {
        "schema": "erdos85-h1-replay-dispatch-v2", "tag": tag,
        "queue_sha256": queue_sha, "worker_sha256": worker_sha,
        "started_unix_ns": started, "finished_unix_ns": finished,
        "wall_ns": finished - started, "returncode": completed.returncode,
        "stdout": completed.stdout, "stderr": completed.stderr,
    }
    destination = args.state_dir / "dispatch" / (
        "accepted" if completed.returncode == 0 else "failed"
    ) / f"{tag}.json"
    atomic_write(destination, canonical_json(receipt))
    return receipt


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--queue", type=Path, required=True)
    parser.add_argument("--state-dir", type=Path, required=True)
    parser.add_argument("--parallelism", type=int, default=1)
    parser.add_argument("--execute", choices=("YES",), required=True,
                        help="explicit launch latch")
    backend = parser.add_mutually_exclusive_group(required=True)
    backend.add_argument("--object-store-root", type=Path)
    backend.add_argument("--s3-bucket")
    parser.add_argument("--aws", default="aws")
    args = parser.parse_args()
    lock_handle = None
    try:
        manifest = load_manifest(args.manifest)
        jobs = load_queue(args.queue)
        if args.parallelism <= 0:
            raise ReplayError("parallelism must be positive")
        approved = manifest.get("max_parallelism")
        if not isinstance(approved, int) or approved <= 0:
            raise ReplayError("manifest.max_parallelism must be positive")
        if args.parallelism > approved:
            raise ReplayError(
                f"parallelism {args.parallelism} exceeds manifest maximum {approved}"
            )
        expected = manifest.get("expected_jobs")
        if not isinstance(expected, int) or expected != len(jobs):
            raise ReplayError(
                f"queue has {len(jobs)} jobs, manifest expects {expected!r}"
            )
        queue_sha = sha256_file(args.queue)
        if manifest.get("queue_sha256") != queue_sha:
            raise ReplayError("queue SHA-256 differs from manifest")
        worker_sha = sha256_file(WORKER)
        if manifest["worker_sha256"] != worker_sha:
            raise ReplayError("worker SHA-256 differs from manifest")
        if manifest.get("single_dispatcher") is not True:
            raise ReplayError("manifest must explicitly require single_dispatcher=true")
        lock_path = Path(manifest["single_writer_lock_path"])
        lock_handle = acquire_single_writer_lock(lock_path)

        start_record = {
            "schema": "erdos85-h1-replay-dispatch-start-v2",
            "manifest_sha256": sha256_file(args.manifest), "queue_sha256": queue_sha,
            "worker_sha256": worker_sha, "jobs": len(jobs),
            "parallelism": args.parallelism, "pid": os.getpid(),
            "single_writer_lock_path": str(lock_path), "started_unix_ns": time.time_ns(),
        }
        atomic_write(args.state_dir / "dispatch" / "START.json", canonical_json(start_record))
        results: list[dict[str, Any]] = []
        with concurrent.futures.ThreadPoolExecutor(max_workers=args.parallelism) as executor:
            futures = [executor.submit(run_job, args, job, queue_sha, worker_sha) for job in jobs]
            for future in concurrent.futures.as_completed(futures):
                results.append(future.result())
        failed = [result for result in results if result["returncode"] != 0]
        end_record = {
            "schema": "erdos85-h1-replay-dispatch-end-v2",
            "manifest_sha256": start_record["manifest_sha256"],
            "queue_sha256": queue_sha, "worker_sha256": worker_sha,
            "jobs": len(jobs), "accepted": len(jobs) - len(failed),
            "failed": len(failed), "failed_tags": sorted(result["tag"] for result in failed),
            "single_writer_lock_path": str(lock_path), "finished_unix_ns": time.time_ns(),
        }
        atomic_write(args.state_dir / "dispatch" / "END.json", canonical_json(end_record))
        print(json.dumps(end_record, sort_keys=True))
        return 0 if not failed else 2
    except (OSError, ReplayError) as error:
        print(f"DISPATCH_ERROR: {error}", file=sys.stderr)
        return 2
    finally:
        if lock_handle is not None:
            fcntl.flock(lock_handle.fileno(), fcntl.LOCK_UN)
            lock_handle.close()


if __name__ == "__main__":
    raise SystemExit(main())
