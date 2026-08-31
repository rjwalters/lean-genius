#!/usr/bin/env python3
"""Create-only, receipt-last builder for the exact 406-job H3/H5 root queue.

This program only derives a durable queue from the independently approved root
manifest.  It never materializes a CNF and has no solver-launch capability.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import subprocess
import tempfile
from pathlib import Path


HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
BUILDER = Path(__file__).resolve()
CELLS = ("h3_b1", "h3_c1", "h3_c2", "h3_dist2",
         "h5_t0", "h5_t1", "h5_t2")
SELECTORS: dict[str, tuple[tuple[int, ...], tuple[int, ...]]] = {
    "h3_b1": ((142, 144, 145, 146, 147, 148, 149),
              (142, 187, 194, 195, 196, 197, 198, 199)),
    "h3_c1": ((142, 144, 145, 146, 147, 148, 149),
              (142, 187, 194, 195, 196, 197, 198, 199)),
    "h3_c2": ((142, 143, 144, 145, 146, 147, 148),
              (142, 194, 195, 196, 197, 198, 199, 207)),
    "h3_dist2": ((142, 143, 144, 145, 146, 147, 148),
                 (142, 193, 196, 197, 198, 199, 200, 201)),
    "h5_t0": ((231, 232, 233, 240, 241, 242, 243),
              (231, 276, 277, 278, 286, 287, 288, 289)),
    "h5_t1": ((231, 232, 238, 239, 240, 241, 242),
              (231, 275, 276, 285, 286, 287, 288, 289)),
    "h5_t2": ((231, 236, 237, 238, 239, 240, 241),
              (231, 274, 275, 284, 285, 286, 287, 288)),
}
APPROVED_ROOT_MANIFEST_SHA256 = (
    "05381a1cf5e80eb480b6e78c4a8dada2573c1cf2f0c55d9ac0bcc4367e3bca76")
APPROVED_FREIGHT_RECEIPT_SHA256 = (
    "6084315bc86ad262533a660aad308639d1d087666b965df47569627c6adf2897")
APPROVED_ROOT_COMMIT = "38b15d484b22d205476baba9f4898c9ffc91044d"
SCHEMA = "erdos85-small-high-root-queue-v1"


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def canonical_json(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def git(repo: Path, *args: str) -> str:
    result = subprocess.run(
        ["git", *args], cwd=repo, text=True, capture_output=True, check=False)
    if result.returncode != 0:
        raise ValueError(result.stderr.strip() or "git command failed")
    return result.stdout.strip()


def require_clean_repo(repo: Path, expected_commit: str | None = None) -> str:
    commit = git(repo, "rev-parse", "HEAD")
    if expected_commit is not None and commit != expected_commit:
        raise ValueError("repository HEAD changed during queue construction")
    if git(repo, "status", "--porcelain=v1", "--untracked-files=all"):
        raise ValueError("repository is dirty")
    return commit


def require_clean_tracked_source(repo: Path, source: Path) -> tuple[str, str]:
    relative = source.resolve().relative_to(repo.resolve()).as_posix()
    if git(repo, "ls-files", "--error-unmatch", "--", relative) != relative:
        raise ValueError("queue builder is not tracked at HEAD")
    if git(repo, "status", "--porcelain=v1", "--", relative):
        raise ValueError("queue builder is dirty")
    historical = subprocess.run(
        ["git", "show", f"HEAD:{relative}"], cwd=repo,
        capture_output=True, check=False)
    if historical.returncode != 0 or historical.stdout != source.read_bytes():
        raise ValueError("queue builder bytes differ from HEAD")
    return git(repo, "rev-parse", "HEAD"), relative


def validate_root_manifest(path: Path, expected_sha256: str) -> tuple[dict, list[str]]:
    if expected_sha256 != APPROVED_ROOT_MANIFEST_SHA256:
        raise ValueError("authorization does not quote the approved root manifest pin")
    raw = path.read_bytes()
    if sha256_bytes(raw) != expected_sha256:
        raise ValueError("root manifest SHA mismatch")
    try:
        manifest = json.loads(raw)
    except json.JSONDecodeError as error:
        raise ValueError("root manifest is not JSON") from error
    if manifest.get("schema") != "erdos85-small-high-cube-jobs-v1":
        raise ValueError("unexpected root manifest schema")
    if manifest.get("lean_commit") != APPROVED_ROOT_COMMIT:
        raise ValueError("root manifest commit mismatch")
    if manifest.get("freight_receipt_sha256") != APPROVED_FREIGHT_RECEIPT_SHA256:
        raise ValueError("root manifest freight pin mismatch")
    if manifest.get("positive_cube_jobs") != 392:
        raise ValueError("root manifest cube count mismatch")
    if manifest.get("negative_cover_jobs") != 14:
        raise ValueError("root manifest cover count mismatch")
    cells = manifest.get("cells")
    if not isinstance(cells, dict) or tuple(cells) != CELLS:
        raise ValueError("root manifest cells are not the exact ordered seven")
    jobs: list[str] = []
    cubes = covers = 0
    for cell_name in CELLS:
        cell = cells[cell_name]
        rows = cell.get("jobs") if isinstance(cell, dict) else None
        if not isinstance(rows, list) or len(rows) != 58:
            raise ValueError(f"{cell_name}: expected exactly 58 jobs")
        left, right = SELECTORS[cell_name]
        cell_left, cell_right = cell.get("left"), cell.get("right")
        if (not isinstance(cell_left, list) or not isinstance(cell_right, list) or
                cell_left != list(left) or cell_right != list(right) or
                any(type(value) is not int
                    for value in [*cell_left, *cell_right])):
            raise ValueError(f"{cell_name}: selector mismatch")
        expected_rows: list[dict[str, object]] = [
            {"id": f"{cell_name}.cover-left", "kind": "cover-left",
             "units": [-value for value in left]},
            {"id": f"{cell_name}.cover-right", "kind": "cover-right",
             "units": [-value for value in right]},
        ]
        for left_index, left_literal in enumerate(left):
            for right_index, right_literal in enumerate(right):
                expected_rows.append({
                    "id": f"{cell_name}.cube-{left_index}-{right_index}",
                    "kind": "cube",
                    "left_index": left_index,
                    "right_index": right_index,
                    "units": [left_literal, right_literal],
                })
        if rows != expected_rows:
            raise ValueError(f"{cell_name}: semantic job mapping mismatch")
        for row in rows:
            if not isinstance(row, dict):
                raise ValueError(f"{cell_name}: malformed job row")
            job_id, kind, units = row.get("id"), row.get("kind"), row.get("units")
            if not isinstance(job_id, str) or not job_id.startswith(cell_name + "."):
                raise ValueError(f"{cell_name}: malformed job id")
            if kind == "cube":
                if set(row) != {"id", "kind", "left_index", "right_index", "units"}:
                    raise ValueError(f"{job_id}: malformed cube row")
                left_index, right_index = row["left_index"], row["right_index"]
                if (type(left_index) is not int or not 0 <= left_index < 7 or
                        type(right_index) is not int or not 0 <= right_index < 8 or
                        job_id != f"{cell_name}.cube-{left_index}-{right_index}"):
                    raise ValueError(f"{job_id}: malformed cube indices")
                if not isinstance(units, list) or len(units) != 2:
                    raise ValueError(f"{job_id}: malformed cube units")
                cubes += 1
            elif kind in ("cover-left", "cover-right"):
                if set(row) != {"id", "kind", "units"}:
                    raise ValueError(f"{job_id}: malformed cover row")
                side = kind.removeprefix("cover-")
                if job_id != f"{cell_name}.cover-{side}":
                    raise ValueError(f"{job_id}: malformed cover id")
                expected_units = 7 if side == "left" else 8
                if not isinstance(units, list) or len(units) != expected_units:
                    raise ValueError(f"{job_id}: malformed cover units")
                covers += 1
            else:
                raise ValueError(f"{job_id}: unexpected job kind")
            if any(type(value) is not int or value == 0 for value in units):
                raise ValueError(f"{job_id}: malformed DIMACS unit")
            jobs.append(job_id)
    if len(jobs) != 406 or len(set(jobs)) != 406 or cubes != 392 or covers != 14:
        raise ValueError("root manifest is not the exact unique 406-job cover")
    return manifest, jobs


def publish_directory(temporary: Path, output: Path) -> None:
    if os.path.lexists(output):
        raise FileExistsError(f"refusing to replace existing output: {output}")
    reserved = False
    try:
        os.mkdir(output)
        reserved = True
        os.rename(temporary / "jobs.txt", output / "jobs.txt")
        os.rename(temporary / "receipt.json", output / "receipt.json")
        temporary.rmdir()
    except FileExistsError as error:
        raise FileExistsError(f"refusing to replace existing output: {output}") from error
    except BaseException:
        if reserved and not (output / "receipt.json").exists():
            shutil.rmtree(output, ignore_errors=True)
        raise


def build(root_manifest: Path, expected_root_sha256: str, output: Path,
          repo: Path = REPO, builder: Path = BUILDER) -> dict[str, object]:
    if os.path.lexists(output):
        raise FileExistsError(f"refusing to replace existing output: {output}")
    commit = require_clean_repo(repo)
    source_commit, relative_builder = require_clean_tracked_source(repo, builder)
    if source_commit != commit:
        raise ValueError("builder source and repository are not at one commit")
    _, jobs = validate_root_manifest(root_manifest, expected_root_sha256)
    queue_bytes = ("\n".join(jobs) + "\n").encode()
    output.parent.mkdir(parents=True, exist_ok=True)
    temporary = Path(tempfile.mkdtemp(prefix=f".{output.name}.", dir=output.parent))
    try:
        queue = temporary / "jobs.txt"
        queue.write_bytes(queue_bytes)
        receipt: dict[str, object] = {
            "schema": SCHEMA,
            "git_commit": commit,
            "builder_source": relative_builder,
            "builder_sha256": sha256_file(builder),
            "root_manifest": str(root_manifest.resolve()),
            "root_manifest_sha256": expected_root_sha256,
            "freight_receipt_sha256": APPROVED_FREIGHT_RECEIPT_SHA256,
            "queue": "jobs.txt",
            "queue_sha256": sha256_bytes(queue_bytes),
            "queue_bytes": len(queue_bytes),
            "jobs": 406,
            "cube_jobs": 392,
            "cover_jobs": 14,
            "cells": list(CELLS),
        }
        (temporary / "receipt.json").write_bytes(canonical_json(receipt))
        require_clean_repo(repo, commit)
        require_clean_tracked_source(repo, builder)
        publish_directory(temporary, output)
        return receipt
    except BaseException:
        shutil.rmtree(temporary, ignore_errors=True)
        raise


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root-manifest", type=Path, required=True)
    parser.add_argument("--expected-root-manifest-sha256", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    receipt = build(args.root_manifest.resolve(),
                    args.expected_root_manifest_sha256, args.output.resolve())
    print(canonical_json(receipt).decode(), end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
