#!/usr/bin/env python3
"""Preflight by default; explicitly launch the approved four-parent third queue."""

from __future__ import annotations

import argparse
import concurrent.futures
import fcntl
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
from datetime import datetime, timezone
from pathlib import Path


BLESSED_QUEUE_RECEIPT_SHA256 = "666538b014b717efb27a16f10dbcc3d61c5eb04487b1ca02cfc3dd34b7ebb332"
SOURCE_WORKER_SHA256 = "f3969c22b9e9551685412ddc4af0e626e4732a2e40322d2b0135ed23de9db6d8"
THIRD_GENERATOR_SHA256 = "81645f1bc5196978c9d724c7a1d13a4d4faad69d427a6d2b68546a5856e68523"
THIRD_MANIFEST_SHA256 = "d50c824b5a473831f542615564c4df9f8f4aab63c207b6218dc8b098ef331402"
WORKER_GENERATOR_SHA256 = "ef366e9814aa150f1bc62267cabb532f74aeac8ea7ec19a9166f91b1998f37be"
QUEUE_SHA256 = "a992dbb7474c2dd7e83b62d087733f42402facc62e9924b210b2d285a6b31879"
CAMPAIGN = Path("/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/campaign-20260825.noindex")
JOB_RE = re.compile(
    r"h3_b1\.cube-0-0\.nested\.cube-0-[0-3]\.third\."
    r"(?:cube-[0-7]-[0-7]|cover-(?:left|right))"
)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def utc() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def validate_worker_receipt(
    receipt: dict[str, object], worker: Path, worker_generator: Path
) -> None:
    expected = {
        "schema": "erdos85-tierA-four-parent-worker-receipt-v1",
        "source_worker_sha256": SOURCE_WORKER_SHA256,
        "third_generator_sha256": THIRD_GENERATOR_SHA256,
        "third_manifest_sha256": THIRD_MANIFEST_SHA256,
        "queue_receipt_sha256": BLESSED_QUEUE_RECEIPT_SHA256,
        "generator_sha256": WORKER_GENERATOR_SHA256,
    }
    for key, value in expected.items():
        if receipt.get(key) != value:
            raise ValueError(f"worker receipt mismatch: {key}")
    if sha256(worker_generator) != WORKER_GENERATOR_SHA256:
        raise ValueError("live worker-generator SHA mismatch")
    if receipt.get("output_worker_sha256") != sha256(worker):
        raise ValueError("generated worker SHA mismatch")


def validate_jobs(queue: Path) -> list[str]:
    data = queue.read_bytes()
    if hashlib.sha256(data).hexdigest() != QUEUE_SHA256:
        raise ValueError("queue SHA mismatch")
    jobs = data.decode().splitlines()
    if len(jobs) != 264 or len(set(jobs)) != 264:
        raise ValueError("queue is not exactly 264 unique jobs")
    if any(JOB_RE.fullmatch(job) is None for job in jobs):
        raise ValueError("queue contains an invalid or unexpected job")
    parents = {job.split(".third.", 1)[0] for job in jobs}
    expected_parents = {
        f"h3_b1.cube-0-0.nested.cube-0-{index}" for index in range(4)
    }
    if parents != expected_parents:
        raise ValueError("queue does not cover exactly the four approved parents")
    if sum(".third.cube-" in job for job in jobs) != 256:
        raise ValueError("queue does not contain exactly 256 cubes")
    if sum(".third.cover-" in job for job in jobs) != 8:
        raise ValueError("queue does not contain exactly 8 covers")
    return jobs


def legacy_processes() -> list[str]:
    result = subprocess.run(
        ["ps", "-axo", "pid=,command="], stdout=subprocess.PIPE, text=True, check=True
    )
    needles = ("run_tierA_396_restart.py", "tierA_job3.py")
    processes = []
    for line in result.stdout.splitlines():
        fields = line.strip().split(maxsplit=1)
        if len(fields) != 2 or int(fields[0]) == os.getpid():
            continue
        if any(needle in fields[1] for needle in needles):
            processes.append(line.strip())
    return processes


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--queue-receipt", type=Path, required=True)
    parser.add_argument("--expected-queue-receipt-sha256", required=True)
    parser.add_argument("--third-generator", type=Path, required=True)
    parser.add_argument("--worker-generator", type=Path, required=True)
    parser.add_argument("--source-worker", type=Path, required=True)
    parser.add_argument("--worker", type=Path, required=True)
    parser.add_argument("--worker-receipt", type=Path, required=True)
    parser.add_argument("--campaign", type=Path, required=True)
    parser.add_argument("--parallelism", type=int, default=4)
    parser.add_argument("--cap", type=int, default=120)
    parser.add_argument("--launch", action="store_true")
    args = parser.parse_args()
    if args.campaign.resolve() != CAMPAIGN:
        raise ValueError("campaign path does not match the worker's pinned campaign")
    if args.expected_queue_receipt_sha256 != BLESSED_QUEUE_RECEIPT_SHA256:
        raise ValueError("authorization does not quote the blessed queue receipt pin")
    if sha256(args.queue_receipt) != BLESSED_QUEUE_RECEIPT_SHA256:
        raise ValueError("queue receipt bytes do not match the blessed pin")
    if sha256(args.third_generator) != THIRD_GENERATOR_SHA256:
        raise ValueError("live third-generator SHA mismatch")
    validation = subprocess.run(
        [
            sys.executable,
            str(args.third_generator),
            "validate-queue",
            "--receipt",
            str(args.queue_receipt),
            "--expected-receipt-sha256",
            BLESSED_QUEUE_RECEIPT_SHA256,
        ],
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
    )
    if validation.returncode or not validation.stdout.startswith("VALID "):
        raise ValueError(f"queue validation failed: {validation.stdout.strip()}")
    queue_receipt = json.loads(args.queue_receipt.read_text())
    manifest = Path(str(queue_receipt.get("manifest", "")))
    queue = Path(str(queue_receipt.get("queue", "")))
    if sha256(manifest) != THIRD_MANIFEST_SHA256:
        raise ValueError("durable third-manifest SHA mismatch")
    if queue_receipt.get("manifest_sha256") != THIRD_MANIFEST_SHA256:
        raise ValueError("queue receipt manifest pin mismatch")
    jobs = validate_jobs(queue)
    supplied_worker_receipt = json.loads(args.worker_receipt.read_text())
    validate_worker_receipt(supplied_worker_receipt, args.worker, args.worker_generator)
    if sha256(args.source_worker) != SOURCE_WORKER_SHA256:
        raise ValueError("live source-worker SHA mismatch")
    with tempfile.TemporaryDirectory(prefix="erdos85-tierA-worker-audit.") as directory:
        regenerated_worker = Path(directory) / "worker.py"
        regenerated_receipt = Path(directory) / "receipt.json"
        regeneration = subprocess.run(
            [
                sys.executable,
                str(args.worker_generator),
                "--source-worker", str(args.source_worker),
                "--third-generator", str(args.third_generator),
                "--third-manifest", str(manifest),
                "--queue-receipt", str(args.queue_receipt),
                "--expected-queue-receipt-sha256", BLESSED_QUEUE_RECEIPT_SHA256,
                "--output", str(regenerated_worker),
                "--receipt-output", str(regenerated_receipt),
            ],
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
        )
        if regeneration.returncode:
            raise ValueError(f"worker regeneration failed: {regeneration.stdout.strip()}")
        if args.worker.read_bytes() != regenerated_worker.read_bytes():
            raise ValueError("supplied worker is not the byte-exact reviewed derivation")
        if supplied_worker_receipt != json.loads(regenerated_receipt.read_text()):
            raise ValueError("supplied worker receipt is not the regenerated receipt")
    environment = {
        key: os.environ[key]
        for key in ("PATH", "HOME", "TMPDIR", "USER", "LOGNAME", "SHELL")
        if key in os.environ
    }
    environment.update(
        {"MODE": "quick", "TIERA_CAP": str(args.cap), "TIERA_MIN_FREE_KB": str(100 * 1024 * 1024)}
    )
    preflight_environment = dict(environment)
    preflight_environment["TIERA_PREFLIGHT_ONLY"] = "1"
    preflight = subprocess.run(
        [sys.executable, str(args.worker), jobs[0]],
        env=preflight_environment,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
    )
    if preflight.returncode or "PREFLIGHT VERIFIED" not in preflight.stdout:
        raise ValueError(f"worker preflight failed: {preflight.stdout.strip()}")
    if not 1 <= args.parallelism <= 8 or not 1 <= args.cap <= 3600:
        raise ValueError("unsafe parallelism or cap")
    processes = legacy_processes()
    if not args.launch:
        print(
            f"PREFLIGHT VERIFIED jobs=264 cubes=256 covers=8 P={args.parallelism} "
            f"mode=quick cap_s={args.cap} launch_blockers={len(processes)}"
        )
        for process in processes:
            print(f"BLOCKER {process}")
        return 0
    if processes:
        raise ValueError("legacy Tier-A process tree still exists; shutdown must precede launch")
    for job in jobs:
        work = args.campaign / "tierA" / job
        if work.exists() and any(work.iterdir()):
            raise ValueError(f"nonempty child directory blocks first launch: {job}")
    events = args.campaign / "ledger/tierA-four-parent-third.events"
    events.parent.mkdir(exist_ok=True)
    with events.open("a+") as stream:
        fcntl.flock(stream.fileno(), fcntl.LOCK_EX)
        stream.write(
            f"{utc()} START receipt_sha256={BLESSED_QUEUE_RECEIPT_SHA256} "
            f"queue_sha256={QUEUE_SHA256} worker_sha256={sha256(args.worker)} "
            f"P={args.parallelism} mode=quick cap_s={args.cap} jobs=264\n"
        )
        stream.flush()
        os.fsync(stream.fileno())

    def run(job: str) -> tuple[str, int]:
        result = subprocess.run([sys.executable, str(args.worker), job], env=environment)
        return job, result.returncode

    failures: list[tuple[str, int]] = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.parallelism) as pool:
        for job, returncode in (future.result() for future in concurrent.futures.as_completed(
            [pool.submit(run, job) for job in jobs]
        )):
            if returncode:
                failures.append((job, returncode))
    with events.open("a+") as stream:
        fcntl.flock(stream.fileno(), fcntl.LOCK_EX)
        stream.write(f"{utc()} END completed=264 failures={len(failures)}\n")
        stream.flush()
        os.fsync(stream.fileno())
    for job, returncode in failures:
        print(f"FAILED rc={returncode} {job}", file=sys.stderr)
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
