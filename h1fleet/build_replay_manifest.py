#!/usr/bin/env python3
"""Freeze a reviewed replay draft and queue into an immutable launch manifest."""

from __future__ import annotations

import argparse
import subprocess
import sys
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


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--draft", type=Path, required=True)
    parser.add_argument("--queue", type=Path, required=True)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    try:
        manifest = load_json(args.draft)
        if manifest.get("schema") != SCHEMA:
            raise ReplayError("draft has wrong replay manifest schema")
        jobs = load_queue(args.queue)
        status = git_value(args.repo, "status", "--porcelain")
        if status:
            raise ReplayError("repository must be clean before manifest freeze")
        manifest.update({
            "repository_commit": git_value(args.repo, "rev-parse", "HEAD"),
            "queue_sha256": sha256_file(args.queue), "expected_jobs": len(jobs),
            "worker_sha256": sha256_file(HERE / "replay_worker.py"),
            "validator_sha256": sha256_file(HERE / "validate_replay_receipt.py"),
            "dispatcher_sha256": sha256_file(HERE / "run_replay_queue.py"),
            "axiom_auditor_sha256": sha256_file(HERE / "audit_replay_leaf.py"),
            "common_sha256": sha256_file(HERE / "replay_common.py"),
            "single_dispatcher": True,
        })
        atomic_write(args.output, canonical_json(manifest))
        load_manifest(args.output)
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
