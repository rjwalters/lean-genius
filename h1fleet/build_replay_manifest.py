#!/usr/bin/env python3
"""Freeze a reviewed replay draft and queue into an immutable launch manifest."""

from __future__ import annotations

import argparse
import hashlib
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

from capacity_queue import (
    load_capacity_index, validate_queue_capacity, validate_queue_tables,
    validate_reindex_receipt,
)
from replay_common import (
    ReplayError, SCHEMA, atomic_write, canonical_json, load_json, load_manifest,
    require_sha, sha256_file, validate_production_compile_fields,
)
from run_replay_queue import load_queue
from build_replay_queue import SCHEMA as QUEUE_BUILD_SCHEMA


HERE = Path(__file__).resolve().parent
OVERLAY_SCHEMA = "erdos85-h1-replay-complete-olean-overlay-v1"
OVERLAY_RECEIPT_SCHEMA = "erdos85-h1-replay-complete-olean-overlay-receipt-v1"
OVERLAY_RECEIPT_FIELDS = {
    "control_files", "entry_count", "git_path", "git_sha256",
    "manifest_path", "manifest_sha256", "overlay_identity_sha256",
    "packages", "producer_path", "producer_sha256", "project_manifest_path",
    "project_manifest_sha256", "project_root", "repo", "schema",
    "source_commit",
}


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


def validate_overlay_freight(
    *, receipt_path: Path, manifest_path: Path, archive_path: Path,
    project_manifest_path: Path, builder_path: Path, source_commit: str,
) -> dict[str, str]:
    """Bind every distinct identity in the combined-overlay freight chain."""
    for path, label in (
        (receipt_path, "overlay build receipt"),
        (manifest_path, "overlay manifest"),
        (archive_path, "combined overlay archive"),
        (project_manifest_path, "project overlay manifest"),
        (builder_path, "overlay builder"),
    ):
        if not path.is_absolute() or path != path.resolve(strict=False):
            raise ReplayError(f"{label} path must be canonical absolute")
        if path.is_symlink() or not path.is_file():
            raise ReplayError(f"{label} must be a regular file")
    receipt = load_json(receipt_path)
    overlay_manifest = load_json(manifest_path)
    if receipt_path.read_bytes() != canonical_json(receipt):
        raise ReplayError("overlay build receipt is not canonical JSON")
    if manifest_path.read_bytes() != canonical_json(overlay_manifest):
        raise ReplayError("overlay manifest is not canonical JSON")
    if set(receipt) != OVERLAY_RECEIPT_FIELDS:
        raise ReplayError("overlay build receipt fields differ from exact schema")
    if receipt.get("schema") != OVERLAY_RECEIPT_SCHEMA:
        raise ReplayError("overlay build receipt has wrong schema")
    if set(overlay_manifest) != {
        "entry_count", "entries", "identity_sha256", "included_extensions", "schema",
    }:
        raise ReplayError("overlay manifest fields differ from exact schema")
    entries = overlay_manifest.get("entries")
    if (
        overlay_manifest.get("schema") != OVERLAY_SCHEMA
        or overlay_manifest.get("included_extensions") != [".olean"]
        or not isinstance(entries, list) or not entries
        or overlay_manifest.get("entry_count") != len(entries)
    ):
        raise ReplayError("overlay manifest identity is malformed")
    paths: list[str] = []
    for row in entries:
        if not isinstance(row, dict) or set(row) != {"bytes", "path", "sha256"}:
            raise ReplayError("overlay manifest row differs from exact schema")
        require_sha(row.get("sha256"), "overlay manifest row.sha256")
        path = row.get("path")
        if (
            not isinstance(path, str) or not path or path.startswith("/")
            or "\\" in path or any(part in ("", ".", "..") for part in path.split("/"))
            or not path.endswith(".olean")
            or type(row.get("bytes")) is not int or row["bytes"] <= 0
        ):
            raise ReplayError("overlay manifest row is malformed")
        paths.append(path)
    if paths != sorted(set(paths)):
        raise ReplayError("overlay manifest paths are not sorted and unique")
    identity = hashlib.sha256(canonical_json(entries)).hexdigest()
    if overlay_manifest.get("identity_sha256") != identity:
        raise ReplayError("overlay manifest tree identity mismatch")
    manifest_sha = sha256_file(manifest_path)
    builder_sha = sha256_file(builder_path)
    project_sha = sha256_file(project_manifest_path)
    project_paths: set[str] = set()
    for line_number, line in enumerate(project_manifest_path.read_text().splitlines(), 1):
        fields = line.split("\t")
        if len(fields) != 2:
            raise ReplayError(f"project overlay manifest line {line_number} is malformed")
        require_sha(fields[0], f"project overlay manifest line {line_number}")
        path = fields[1]
        if (
            not path or path.startswith("/") or "\\" in path
            or any(part in ("", ".", "..") for part in path.split("/"))
            or not path.endswith(".olean") or path.startswith("Proofs/Generated/")
            or path in project_paths
        ):
            raise ReplayError(f"project overlay manifest line {line_number} path is malformed")
        project_paths.add(path)
    if not project_paths:
        raise ReplayError("project overlay manifest is empty")
    for key in (
        "git_sha256", "manifest_sha256", "overlay_identity_sha256",
        "producer_sha256", "project_manifest_sha256",
    ):
        require_sha(receipt.get(key), f"overlay build receipt.{key}")
    if (
        receipt["manifest_path"] != "manifest.json"
        or receipt["manifest_sha256"] != manifest_sha
        or receipt["overlay_identity_sha256"] != identity
        or Path(receipt.get("producer_path", "")).resolve(strict=False) != builder_path
        or receipt["producer_sha256"] != builder_sha
        or Path(receipt.get("project_manifest_path", "")).resolve(strict=False)
        != project_manifest_path
        or receipt["project_manifest_sha256"] != project_sha
        or receipt["source_commit"] != source_commit
        or receipt["entry_count"] != len(entries)
    ):
        raise ReplayError("overlay build receipt crosslink mismatch")
    for key in ("git_path", "producer_path", "project_manifest_path", "project_root", "repo"):
        if not isinstance(receipt.get(key), str) or not receipt[key]:
            raise ReplayError(f"overlay build receipt.{key} is malformed")
    controls = receipt.get("control_files")
    if not isinstance(controls, list) or len(controls) != 3:
        raise ReplayError("overlay build receipt control-file census is malformed")
    for row in controls:
        if not isinstance(row, dict) or set(row) != {"blob_oid", "bytes", "path", "sha256"}:
            raise ReplayError("overlay build receipt control row differs from exact schema")
        require_sha(row.get("sha256"), "overlay control.sha256")
        if (not isinstance(row.get("blob_oid"), str)
                or re.fullmatch(r"[0-9a-f]{40}", row["blob_oid"]) is None
                or type(row.get("bytes")) is not int or row["bytes"] <= 0
                or not isinstance(row.get("path"), str) or not row["path"]):
            raise ReplayError("overlay build receipt control row is malformed")
    if [row["path"] for row in controls] != [
        "proofs/lean-toolchain", "proofs/lakefile.toml", "proofs/lake-manifest.json",
    ]:
        raise ReplayError("overlay build receipt control paths differ from exact census")
    packages = receipt.get("packages")
    if not isinstance(packages, list) or not packages:
        raise ReplayError("overlay build receipt package census is empty")
    package_fields = {
        "build_root", "facade", "head", "manifest_url", "name",
        "normalized_remote", "rev",
    }
    names: set[str] = set()
    remotes: set[str] = set()
    for package in packages:
        if not isinstance(package, dict) or set(package) != package_fields:
            raise ReplayError("overlay build receipt package row differs from exact schema")
        if not all(isinstance(package[key], str) and package[key] for key in package_fields):
            raise ReplayError("overlay build receipt package row is malformed")
        if (
            package["head"] != package["rev"]
            or re.fullmatch(r"[0-9a-f]{40}", package["head"]) is None
            or re.fullmatch(r"[A-Za-z][A-Za-z0-9_-]*", package["name"]) is None
            or re.fullmatch(r"github\.com/[^/]+/[^/]+", package["normalized_remote"]) is None
            or package["name"] in names or package["normalized_remote"] in remotes
        ):
            raise ReplayError("overlay build receipt package revision mismatch")
        names.add(package["name"])
        remotes.add(package["normalized_remote"])
    if not archive_path.is_file() or archive_path.stat().st_size <= 0:
        raise ReplayError("combined overlay archive is empty or missing")
    return {
        "overlay_builder_sha256": builder_sha,
        "overlay_project_manifest_sha256": project_sha,
        "overlay_build_receipt_sha256": sha256_file(receipt_path),
        "overlay_manifest_sha256": manifest_sha,
        "overlay_identity_sha256": identity,
        "overlay_archive_sha256": sha256_file(archive_path),
    }


def validate_manifest_bytes(value: bytes) -> None:
    with tempfile.TemporaryDirectory() as temporary:
        candidate = Path(temporary) / "candidate.json"
        atomic_write(candidate, value)
        load_manifest(candidate)


def publish_validated_manifest(output: Path, value: bytes, before_link=None) -> None:
    validate_manifest_bytes(value)
    output.parent.mkdir(parents=True, exist_ok=True)
    handle, temporary_name = tempfile.mkstemp(
        prefix=f".{output.name}.freeze-", dir=output.parent)
    temporary = Path(temporary_name)
    published = False
    try:
        with os.fdopen(handle, "wb") as stream:
            stream.write(value)
            stream.flush()
            os.fsync(stream.fileno())
        if before_link is not None:
            before_link()
        os.link(temporary, output)
        published = True
        directory = os.open(output.parent, os.O_RDONLY)
        try:
            os.fsync(directory)
        finally:
            os.close(directory)
    except BaseException:
        if published:
            try:
                if output.stat().st_ino == temporary.stat().st_ino:
                    output.unlink()
            except FileNotFoundError:
                pass
        raise
    finally:
        temporary.unlink(missing_ok=True)


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
    parser.add_argument("--overlay-build-receipt", type=Path, required=True)
    parser.add_argument("--overlay-manifest", type=Path, required=True)
    parser.add_argument("--overlay-archive", type=Path, required=True)
    parser.add_argument("--overlay-project-manifest", type=Path, required=True)
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
        overlay_builder = HERE / "build_replay_overlay.py"
        hashed_paths = (
            replay_generator, overlay_builder,
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
        overlay_fields = validate_overlay_freight(
            receipt_path=args.overlay_build_receipt,
            manifest_path=args.overlay_manifest,
            archive_path=args.overlay_archive,
            project_manifest_path=args.overlay_project_manifest,
            builder_path=overlay_builder,
            source_commit=head,
        )
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
            **overlay_fields,
        })
        manifest.pop("overlay_sha256", None)
        validate_production_compile_fields(manifest)
        value = canonical_json(manifest)
        validate_manifest_bytes(value)
        def revalidate_before_link() -> None:
            if validate_overlay_freight(
                receipt_path=args.overlay_build_receipt,
                manifest_path=args.overlay_manifest,
                archive_path=args.overlay_archive,
                project_manifest_path=args.overlay_project_manifest,
                builder_path=overlay_builder,
                source_commit=head,
            ) != overlay_fields:
                raise ReplayError("overlay freight changed while freezing manifest")
            if (git_value(repo, "rev-parse", "HEAD") != head
                    or git_value(repo, "status", "--porcelain")):
                raise ReplayError("repository changed while freezing manifest")
        # Validate again inside the publication helper so future callers cannot
        # accidentally publish first and discover schema failure afterward.
        publish_validated_manifest(args.output, value, revalidate_before_link)
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
