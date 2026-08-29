#!/usr/bin/env python3
"""Freeze a reviewed replay draft and queue into an immutable launch manifest."""

from __future__ import annotations

import argparse
import subprocess
import sys
import tempfile
from pathlib import Path

from replay_common import ReplayError, SCHEMA, atomic_write, canonical_json, load_json, load_manifest, sha256_file
from run_replay_queue import load_queue


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


def validate_manifest_bytes(value: bytes) -> None:
    with tempfile.TemporaryDirectory() as temporary:
        candidate = Path(temporary) / "candidate.json"
        atomic_write(candidate, value)
        load_manifest(candidate)


def publish_validated_manifest(output: Path, value: bytes) -> None:
    validate_manifest_bytes(value)
    atomic_write(output, value)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--draft", type=Path, required=True)
    parser.add_argument("--queue", type=Path, required=True)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
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
        status = git_value(repo, "status", "--porcelain")
        if status:
            raise ReplayError("repository must be clean before manifest freeze")
        head = git_value(repo, "rev-parse", "HEAD")
        aggregate_generator = (
            repo / "research/problems/erdos-85-wip-01/sat49/"
            "generate_h1_v2_lean_aggregate.py"
        )
        hashed_paths = (
            HERE / "replay_worker.py", HERE / "validate_replay_receipt.py",
            HERE / "run_replay_queue.py", HERE / "audit_replay_leaf.py",
            HERE / "replay_common.py", HERE / "CLOUD_LEAN_REPLAY_STAGE_SPEC.md",
            aggregate_generator,
        )
        for path in hashed_paths:
            require_tracked_at_head(repo, path)
        manifest.update({
            "repository_commit": head,
            "queue_sha256": sha256_file(args.queue), "expected_jobs": len(jobs),
            "worker_sha256": sha256_file(HERE / "replay_worker.py"),
            "validator_sha256": sha256_file(HERE / "validate_replay_receipt.py"),
            "dispatcher_sha256": sha256_file(HERE / "run_replay_queue.py"),
            "axiom_auditor_sha256": sha256_file(HERE / "audit_replay_leaf.py"),
            "common_sha256": sha256_file(HERE / "replay_common.py"),
            "receipt_schema_sha256": sha256_file(HERE / "CLOUD_LEAN_REPLAY_STAGE_SPEC.md"),
            "aggregate_generator_sha256": sha256_file(aggregate_generator),
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
