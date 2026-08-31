#!/usr/bin/env python3
"""Freeze a reviewed replay draft and queue into an immutable launch manifest."""

from __future__ import annotations

import argparse
import subprocess
import sys
import tempfile
from pathlib import Path

from capacity_queue import (
    load_capacity_index, validate_queue_capacity, validate_queue_tables,
    validate_reindex_receipt,
)
from replay_common import ReplayError, SCHEMA, atomic_write, canonical_json, load_json, load_manifest, require_sha, sha256_file
from run_replay_queue import load_queue
from build_replay_queue import SCHEMA as QUEUE_BUILD_SCHEMA


HERE = Path(__file__).resolve().parent


def git_value(repo: Path, *arguments: str) -> str:
    result = subprocess.run(
        ["git", *arguments], cwd=repo, text=True, capture_output=True, check=False
    )
    if result.returncode != 0:
        raise ReplayError(f"git {' '.join(arguments)} failed: {result.stderr.strip()}")
    return result.stdout.strip()


def require_tracked_at_head(repo: Path, path: Path) -> None:
    try:
        relative = path.resolve().relative_to(repo)
    except ValueError as error:
        raise ReplayError(f"freight input is outside repository: {path}") from error
    for arguments in (
        ("ls-files", "--error-unmatch", str(relative)),
        ("cat-file", "-e", f"HEAD:{relative}"),
    ):
        git_value(repo, *arguments)


def generator_identity_fields(generator: Path) -> dict[str, str]:
    """Bind both legacy source-format fields to the executable generator.

    Replay leaves have no separate template file: ``generate_replay_leaf.py``
    both renders the template and drives its create-only publication.  Keeping
    this mapping in the freezer prevents stale draft pins from surviving a
    successful freeze.
    """
    identity = sha256_file(generator)
    return {"generator_sha256": identity, "template_sha256": identity}


def validate_manifest_bytes(value: bytes) -> None:
    with tempfile.TemporaryDirectory() as temporary:
        candidate = Path(temporary) / "candidate.json"
        atomic_write(candidate, value)
        load_manifest(candidate)


def publish_validated_manifest(output: Path, value: bytes) -> None:
    validate_manifest_bytes(value)
    atomic_write(output, value)


def validate_queue_build_receipt(
    receipt: dict, queue: Path, capacity_index: Path, terminal_index: Path,
    inventory_sha256: str,
    expected_jobs: int, require_complete: bool,
) -> str:
    expected_fields = {
        "schema", "inventory_sha256", "certificate_index_sha256",
        "terminal_index_sha256", "output_sha256", "emitted_jobs",
        "require_complete",
    }
    if set(receipt) != expected_fields:
        raise ReplayError("queue-build receipt fields differ from exact schema")
    if receipt.get("schema") != QUEUE_BUILD_SCHEMA:
        raise ReplayError("queue-build receipt has wrong schema")
    for key in ("inventory_sha256", "certificate_index_sha256",
                "terminal_index_sha256", "output_sha256"):
        require_sha(receipt.get(key), f"queue-build receipt.{key}")
    if receipt["output_sha256"] != sha256_file(queue):
        raise ReplayError("queue-build receipt output hash mismatch")
    if receipt["certificate_index_sha256"] != sha256_file(capacity_index):
        raise ReplayError("queue-build receipt capacity-index hash mismatch")
    if receipt["terminal_index_sha256"] != sha256_file(terminal_index):
        raise ReplayError("queue-build receipt terminal-index hash mismatch")
    if receipt["inventory_sha256"] != inventory_sha256:
        raise ReplayError("queue-build receipt inventory hash mismatch")
    if receipt.get("emitted_jobs") != expected_jobs:
        raise ReplayError("queue-build receipt job count mismatch")
    if receipt.get("require_complete") is not require_complete:
        raise ReplayError("queue-build receipt completeness mismatch")
    return receipt["terminal_index_sha256"]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--draft", type=Path, required=True)
    parser.add_argument("--queue", type=Path, required=True)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--capacity-index", type=Path, required=True)
    parser.add_argument("--capacity-reindex-receipt", type=Path, required=True)
    parser.add_argument("--queue-build-receipt", type=Path, required=True)
    parser.add_argument("--terminal-index", type=Path, required=True)
    parser.add_argument("--require-complete-capacity-queue", action="store_true")
    args = parser.parse_args()
    try:
        repo = args.repo.resolve()
        script_repo = Path(git_value(HERE, "rev-parse", "--show-toplevel")).resolve()
        if repo != script_repo:
            raise ReplayError("--repo must be the worktree containing replay scripts")
        try:
            args.output.resolve().relative_to(repo)
        except ValueError:
            pass
        else:
            raise ReplayError("frozen manifest output must be outside the repository")
        manifest = load_json(args.draft)
        if manifest.get("schema") != SCHEMA:
            raise ReplayError("draft has wrong replay manifest schema")
        jobs = load_queue(args.queue)
        queue_build_receipt = load_json(args.queue_build_receipt)
        terminal_index_sha256 = validate_queue_build_receipt(
            queue_build_receipt, args.queue, args.capacity_index, args.terminal_index,
            manifest.get("inventory_sha256", ""), len(jobs),
            args.require_complete_capacity_queue,
        )
        capacity = load_capacity_index(args.capacity_index)
        reindex_receipt = validate_reindex_receipt(
            args.capacity_reindex_receipt, args.capacity_index,
            manifest.get("inventory_sha256", ""),
        )
        if reindex_receipt.get("emitted_rows") != len(capacity):
            raise ReplayError("capacity reindex receipt row count mismatch")
        dropped = set(reindex_receipt["dropped_outside_capacity_tags"])
        if dropped.intersection(capacity):
            raise ReplayError("capacity reindex receipt drops an emitted capacity tag")
        if (
            args.require_complete_capacity_queue
            and reindex_receipt.get("require_complete") is not True
        ):
            raise ReplayError("complete replay freeze requires a complete reindex receipt")
        validate_queue_capacity(jobs, capacity, args.require_complete_capacity_queue)
        validate_queue_tables(jobs)
        status = git_value(repo, "status", "--porcelain")
        if status:
            raise ReplayError("repository must be clean before manifest freeze")
        head = git_value(repo, "rev-parse", "HEAD")
        aggregate_generator = (
            repo / "research/problems/erdos-85-wip-01/sat49/"
            "generate_h1_v2_lean_aggregate.py"
        )
        stub_generator = (
            repo / "research/problems/erdos-85-wip-01/sat49/"
            "generate_h1_v2_lean_stubs.py"
        )
        capacity_exporter = (
            repo / "research/problems/erdos-85-wip-01/sat49/"
            "filter_h1_capacity_inventory.py"
        )
        capacity_reindexer = (
            repo / "research/problems/erdos-85-wip-01/sat49/"
            "reindex_h1_v2_capacity_certificates.py"
        )
        queue_builder = HERE / "build_replay_queue.py"
        replay_generator = HERE / "generate_replay_leaf.py"
        hashed_paths = (
            replay_generator,
            HERE / "replay_worker.py", HERE / "validate_replay_receipt.py",
            HERE / "run_replay_queue.py", HERE / "audit_replay_leaf.py",
            HERE / "replay_common.py", HERE / "CLOUD_LEAN_REPLAY_STAGE_SPEC.md",
            aggregate_generator,
            HERE / "capacity_queue.py", stub_generator,
            capacity_exporter, capacity_reindexer,
            queue_builder,
        )
        for path in hashed_paths:
            require_tracked_at_head(repo, path)
        manifest.update({
            "repository_commit": head,
            "queue_sha256": sha256_file(args.queue), "expected_jobs": len(jobs),
            **generator_identity_fields(replay_generator),
            "worker_sha256": sha256_file(HERE / "replay_worker.py"),
            "validator_sha256": sha256_file(HERE / "validate_replay_receipt.py"),
            "dispatcher_sha256": sha256_file(HERE / "run_replay_queue.py"),
            "axiom_auditor_sha256": sha256_file(HERE / "audit_replay_leaf.py"),
            "common_sha256": sha256_file(HERE / "replay_common.py"),
            "receipt_schema_sha256": sha256_file(HERE / "CLOUD_LEAN_REPLAY_STAGE_SPEC.md"),
            "aggregate_generator_sha256": sha256_file(aggregate_generator),
            "stub_generator_sha256": sha256_file(stub_generator),
            "capacity_exporter_sha256": sha256_file(capacity_exporter),
            "capacity_reindexer_sha256": sha256_file(capacity_reindexer),
            "capacity_queue_validator_sha256": sha256_file(HERE / "capacity_queue.py"),
            "queue_builder_sha256": sha256_file(queue_builder),
            "queue_build_receipt_sha256": sha256_file(args.queue_build_receipt),
            "terminal_index_sha256": terminal_index_sha256,
            "capacity_index_sha256": sha256_file(args.capacity_index),
            "capacity_reindex_receipt_sha256": sha256_file(args.capacity_reindex_receipt),
            "complete_capacity_queue": args.require_complete_capacity_queue,
            "single_dispatcher": True,
        })
        value = canonical_json(manifest)
        validate_manifest_bytes(value)
        if git_value(repo, "rev-parse", "HEAD") != head or git_value(repo, "status", "--porcelain"):
            raise ReplayError("repository changed while freezing manifest")
        # Validate again inside the publication helper so future callers cannot
        # accidentally publish first and discover schema failure afterward.
        publish_validated_manifest(args.output, value)
        print(
            f"FROZEN manifest={args.output} sha256={sha256_file(args.output)} "
            f"jobs={len(jobs)} commit={manifest['repository_commit']}"
        )
        return 0
    except (OSError, ReplayError) as error:
        print(f"MANIFEST_ERROR: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
