#!/usr/bin/env python3
"""Receipt an inert end-to-end preflight of the exact 406-job root queue.

There is deliberately no launch mode in this program.  It validates the two
independently reviewed artifacts, invokes the worker only with
TIERA_PREFLIGHT_ONLY=1, proves the reserved namespace remains absent, and
publishes a create-only canonical receipt.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import os
import stat
import subprocess
import tempfile
from pathlib import Path


HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
CONTROLLER = Path(__file__).resolve()
CONTROLLER_REPO_PATH = (
    "research/problems/erdos-85-wip-01/sat49/run_tierA_root_queue.py")
QUEUE_RECEIPT_SHA256 = (
    "fa07876764990816f4d7a5940b09958c33d86676edcc3cddcbabad32b482d103")
QUEUE_SHA256 = (
    "91cd2b14a3d0f5a3b9d30d94a4765928a885da74f428a754aadcda5c9ada504b")
WORKER_RECEIPT_SHA256 = (
    "35d1f8a4f616630ca60cd37ee364d9bb81080299695f11d0a6fbac11656db108")
WORKER_SHA256 = (
    "137e57dc3884fc2f61986cb0ed56762e3fe93708331e8f600fc83aa535e5d22a")
ROOT_MANIFEST_SHA256 = (
    "05381a1cf5e80eb480b6e78c4a8dada2573c1cf2f0c55d9ac0bcc4367e3bca76")
FREIGHT_RECEIPT_SHA256 = (
    "6084315bc86ad262533a660aad308639d1d087666b965df47569627c6adf2897")
WORK_ROOT = Path(
    "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/"
    "campaign-20260825.noindex/tierA-root-dff2402069-fa078767")
SCHEMA = "erdos85-tierA-root-composed-preflight-v1"
LINEAGE_SCHEMA = "erdos85-tierA-root-lineage-v1"


def canonical_json(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load_canonical_pinned(path: Path, expected_sha256: str, label: str) -> dict:
    raw = path.read_bytes()
    if sha256_bytes(raw) != expected_sha256:
        raise ValueError(f"{label} SHA mismatch")
    try:
        value = json.loads(raw)
    except json.JSONDecodeError as error:
        raise ValueError(f"{label} is not JSON") from error
    if not isinstance(value, dict) or raw != canonical_json(value):
        raise ValueError(f"{label} is not canonical JSON")
    return value


def git(repo: Path, *args: str) -> str:
    result = subprocess.run(
        ["git", *args], cwd=repo, text=True, capture_output=True, check=False)
    if result.returncode != 0:
        raise ValueError(result.stderr.strip() or "git command failed")
    return result.stdout.strip()


def require_clean_controller(repo: Path, source: Path) -> tuple[str, str]:
    commit = git(repo, "rev-parse", "HEAD")
    if git(repo, "status", "--porcelain=v1", "--untracked-files=all"):
        raise ValueError("repository is dirty")
    relative = source.resolve().relative_to(repo.resolve()).as_posix()
    if relative != CONTROLLER_REPO_PATH:
        raise ValueError("controller has unexpected repo path")
    if git(repo, "ls-files", "--error-unmatch", "--", relative) != relative:
        raise ValueError("controller is not tracked at HEAD")
    historical = subprocess.run(
        ["git", "show", f"{commit}:{relative}"], cwd=repo,
        capture_output=True, check=False)
    if historical.returncode != 0 or historical.stdout != source.read_bytes():
        raise ValueError("controller bytes differ from HEAD")
    return commit, relative


def validate_inputs(queue_receipt_path: Path, worker_receipt_path: Path,
                    worker: Path) -> tuple[list[str], dict, dict]:
    queue_receipt = load_canonical_pinned(
        queue_receipt_path, QUEUE_RECEIPT_SHA256, "queue receipt")
    worker_receipt = load_canonical_pinned(
        worker_receipt_path, WORKER_RECEIPT_SHA256, "worker receipt")
    if queue_receipt.get("schema") != "erdos85-small-high-root-queue-v1":
        raise ValueError("queue receipt schema mismatch")
    if (queue_receipt.get("queue_sha256") != QUEUE_SHA256 or
            queue_receipt.get("root_manifest_sha256") != ROOT_MANIFEST_SHA256 or
            queue_receipt.get("freight_receipt_sha256") != FREIGHT_RECEIPT_SHA256 or
            queue_receipt.get("jobs") != 406 or
            queue_receipt.get("cube_jobs") != 392 or
            queue_receipt.get("cover_jobs") != 14 or
            queue_receipt.get("queue") != "jobs.txt"):
        raise ValueError("queue receipt content mismatch")
    queue = queue_receipt_path.parent / "jobs.txt"
    raw_queue = queue.read_bytes()
    if sha256_bytes(raw_queue) != QUEUE_SHA256:
        raise ValueError("queue bytes mismatch")
    try:
        jobs = raw_queue.decode("ascii").splitlines()
    except UnicodeDecodeError as error:
        raise ValueError("queue is not ASCII") from error
    if len(jobs) != 406 or len(set(jobs)) != 406 or raw_queue != (
            "\n".join(jobs) + "\n").encode():
        raise ValueError("queue is not exactly 406 unique newline-delimited jobs")
    if worker_receipt.get("schema") != "erdos85-tierA-root-worker-receipt-v1":
        raise ValueError("worker receipt schema mismatch")
    if (worker_receipt.get("output_worker_sha256") != WORKER_SHA256 or
            worker_receipt.get("queue_receipt_sha256") != QUEUE_RECEIPT_SHA256 or
            worker_receipt.get("queue_sha256") != QUEUE_SHA256 or
            worker_receipt.get("root_manifest_sha256") != ROOT_MANIFEST_SHA256 or
            worker_receipt.get("freight_receipt_sha256") != FREIGHT_RECEIPT_SHA256 or
            worker_receipt.get("lineage_schema") != LINEAGE_SCHEMA or
            worker_receipt.get("work_root") != str(WORK_ROOT) or
            worker_receipt.get("jobs") != 406 or
            worker_receipt.get("header_rewrite") is not False):
        raise ValueError("worker receipt content mismatch")
    if sha256_file(worker) != WORKER_SHA256:
        raise ValueError("worker bytes mismatch")
    return jobs, queue_receipt, worker_receipt


def legacy_snapshot(legacy_root: Path, jobs: list[str]) -> tuple[str, int]:
    rows: list[list[object]] = []
    for job in jobs:
        job_root = legacy_root / job
        if not os.path.lexists(job_root):
            rows.append([job, "absent"])
            continue
        for path in [job_root, *sorted(job_root.rglob("*"))]:
            info = path.lstat()
            relative = path.relative_to(legacy_root).as_posix()
            target = os.readlink(path) if stat.S_ISLNK(info.st_mode) else None
            rows.append([
                relative, info.st_mode, info.st_size, info.st_mtime_ns,
                info.st_ino, target,
            ])
    return sha256_bytes(canonical_json(rows)), len(rows)


def lineage_marker(commit: str, source: str, controller_sha256: str) -> dict[str, str]:
    return {
        "schema": LINEAGE_SCHEMA,
        "work_root": str(WORK_ROOT),
        "worker_sha256": WORKER_SHA256,
        "worker_receipt_sha256": WORKER_RECEIPT_SHA256,
        "queue_receipt_sha256": QUEUE_RECEIPT_SHA256,
        "queue_sha256": QUEUE_SHA256,
        "root_manifest_sha256": ROOT_MANIFEST_SHA256,
        "freight_receipt_sha256": FREIGHT_RECEIPT_SHA256,
        "controller_git_commit": commit,
        "controller_source": source,
        "controller_sha256": controller_sha256,
    }


def run_worker_preflights(worker: Path, jobs: list[str], parallelism: int) -> str:
    if not 1 <= parallelism <= 8:
        raise ValueError("parallelism must be between 1 and 8")
    environment = {
        key: os.environ[key]
        for key in ("PATH", "HOME", "TMPDIR", "USER", "LOGNAME", "SHELL")
        if key in os.environ
    }
    environment.update({
        "TIERA_PREFLIGHT_ONLY": "1",
        "MODE": "quick",
        "TIERA_MIN_FREE_KB": str(100 * 1024 * 1024),
    })

    def run(job: str) -> tuple[str, str]:
        result = subprocess.run(
            [os.fspath(worker), job], env=environment,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        expected = (
            f"PREFLIGHT VERIFIED job={job} mode=quick kind=root "
            f"manifest_sha256={ROOT_MANIFEST_SHA256}\n")
        if result.returncode != 0 or result.stdout != expected:
            raise ValueError(
                f"worker preflight failed for {job}: rc={result.returncode} "
                f"output={result.stdout.strip()!r}")
        return job, result.stdout

    outputs: dict[str, str] = {}
    with concurrent.futures.ThreadPoolExecutor(max_workers=parallelism) as pool:
        futures = [pool.submit(run, job) for job in jobs]
        for future in concurrent.futures.as_completed(futures):
            job, output = future.result()
            outputs[job] = output
    ordered = [[job, outputs[job]] for job in jobs]
    return sha256_bytes(canonical_json(ordered))


def publish_create_only(raw: bytes, output: Path) -> None:
    output.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary_name = tempfile.mkstemp(
        prefix=f".{output.name}.", suffix=".tmp", dir=output.parent)
    temporary = Path(temporary_name)
    try:
        with os.fdopen(fd, "wb") as stream:
            stream.write(raw)
        try:
            os.link(temporary, output)
        except FileExistsError as error:
            raise FileExistsError(
                f"refusing to replace existing output: {output}") from error
    finally:
        temporary.unlink(missing_ok=True)


def reject_protected_output(output: Path, protected_roots: tuple[Path, ...]) -> None:
    resolved = output.resolve()
    for root in protected_roots:
        protected = root.resolve()
        if resolved == protected or protected in resolved.parents:
            raise ValueError(f"receipt output aliases protected evidence tree: {root}")


def preflight(queue_receipt_path: Path, worker_receipt_path: Path,
              worker: Path, output: Path, parallelism: int,
              repo: Path = REPO, controller: Path = CONTROLLER) -> dict[str, object]:
    if os.path.lexists(WORK_ROOT):
        raise ValueError("fresh work root is already occupied")
    if os.path.lexists(output):
        raise FileExistsError(f"refusing to replace existing output: {output}")
    legacy_root = WORK_ROOT.parent / "tierA"
    reject_protected_output(output, (WORK_ROOT, legacy_root))
    commit, relative_source = require_clean_controller(repo, controller)
    controller_sha256 = sha256_file(controller)
    jobs, _, _ = validate_inputs(queue_receipt_path, worker_receipt_path, worker)
    legacy_before, legacy_entries = legacy_snapshot(legacy_root, jobs)
    outputs_sha256 = run_worker_preflights(worker, jobs, parallelism)
    legacy_after, legacy_entries_after = legacy_snapshot(legacy_root, jobs)
    if legacy_after != legacy_before or legacy_entries_after != legacy_entries:
        raise ValueError("legacy evidence changed during inert preflight")
    if os.path.lexists(WORK_ROOT):
        raise ValueError("worker preflight created the reserved namespace")
    final_commit, final_source = require_clean_controller(repo, controller)
    if (final_commit, final_source) != (commit, relative_source):
        raise ValueError("controller provenance changed during inert preflight")
    marker = lineage_marker(commit, relative_source, controller_sha256)
    receipt: dict[str, object] = {
        "schema": SCHEMA,
        "git_commit": commit,
        "controller_source": relative_source,
        "controller_sha256": controller_sha256,
        "worker": str(worker.resolve()),
        "worker_sha256": WORKER_SHA256,
        "worker_receipt": str(worker_receipt_path.resolve()),
        "worker_receipt_sha256": WORKER_RECEIPT_SHA256,
        "queue_receipt": str(queue_receipt_path.resolve()),
        "queue_receipt_sha256": QUEUE_RECEIPT_SHA256,
        "queue_sha256": QUEUE_SHA256,
        "root_manifest_sha256": ROOT_MANIFEST_SHA256,
        "freight_receipt_sha256": FREIGHT_RECEIPT_SHA256,
        "work_root": str(WORK_ROOT),
        "work_root_absent_before_and_after": True,
        "jobs": 406,
        "preflight_parallelism": parallelism,
        "preflight_outputs_sha256": outputs_sha256,
        "legacy_root": str(legacy_root),
        "legacy_entries": legacy_entries,
        "legacy_snapshot_before_sha256": legacy_before,
        "legacy_snapshot_after_sha256": legacy_after,
        "lineage_marker": marker,
        "lineage_marker_sha256": sha256_bytes(canonical_json(marker)),
        "launch_capability": False,
    }
    publish_create_only(canonical_json(receipt), output)
    return receipt


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--queue-receipt", type=Path, required=True)
    parser.add_argument("--worker-receipt", type=Path, required=True)
    parser.add_argument("--worker", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--parallelism", type=int, default=4)
    args = parser.parse_args()
    receipt = preflight(
        args.queue_receipt.resolve(), args.worker_receipt.resolve(),
        args.worker.resolve(), args.output.resolve(), args.parallelism)
    print(canonical_json(receipt).decode(), end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
