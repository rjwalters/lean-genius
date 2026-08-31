#!/usr/bin/env python3
"""Create the reviewed H1 leaf/aggregate/adapter tree, then stop for review.

This driver deliberately has no commit, finalizer, cache-snapshot, cold-build,
object-upload, or AWS-launch action.  Its successful terminal state is an
uncommitted source tree plus a transcript for the mandatory review boundary.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path, PurePosixPath
from typing import Callable

SCHEMA = "erdos85-h1-replay-to-aggregate-transcript-v1"
LEAF_INDEX_SCHEMA = "erdos85-h1-leaf-module-index-v1"
MATERIALIZATION_SCHEMA = "erdos85-h1-replay-leaf-materialization-v1"
LAYOUT_SCHEMA = "erdos85-h1-v2-aggregate-layout-v1"
ADAPTER_SCHEMA = "erdos85-h1-post-aggregate-adapter-generation-v1"
EXPECTED_LEAVES = 13351
PROFILE_COUNTS = [1485, 3617, 4717, 2693, 839]
LEAF_FIELDS = {"local_index", "orbit", "packed_lrat_sha256", "profile", "source_bytes",
               "source_module", "source_path", "source_sha256"}
MATERIALIZATION_FIELDS = {"certificate_gzip_bytes", "certificate_gzip_sha256", "certificate_key",
    "compact_lrat_bytes", "compact_lrat_path", "compact_lrat_sha256", "local_index", "module",
    "olean_artifact_key", "olean_bytes", "olean_path", "olean_sha256", "orbit", "profile",
    "recompilable_from_tree", "replay_ready_key", "replay_ready_sha256", "receipt_key",
    "receipt_sha256", "source_artifact_key", "source_bytes", "source_path", "source_sha256", "theorem"}
LAYOUT_FIELDS = {"bank_size", "inputs", "inventory_contract", "leaf_count", "leaf_members_sha256",
                 "modules", "prefixes", "profile_bank_counts", "schema", "top_module"}
LAYOUT_MODULE_FIELDS = {"direct_import_count", "direct_imports", "file", "kind", "members", "module",
                        "source_bytes", "source_sha256", "theorem"}
ADAPTER_FIELDS = {"aggregate_layout_path", "aggregate_layout_sha256", "aggregate_source_root",
    "aggregate_sources_identity_sha256", "capacity_index_path", "capacity_index_sha256",
    "capacity_reindex_receipt_path", "capacity_reindex_receipt_sha256", "generator_sha256",
    "generator_source", "input_top_module", "input_top_path", "input_top_repo_path",
    "input_top_sha256", "input_top_theorem", "leaf_count", "leaf_module_index_path",
    "leaf_module_index_sha256", "output_bytes", "output_path", "output_sha256",
    "output_source_module", "output_theorem", "repo", "schema"}
COMMIT = re.compile(r"[0-9a-f]{40}")
SHA256 = re.compile(r"[0-9a-f]{64}")
LEAF_PREFIX = "Proofs.Generated.H1Leaves"
AGGREGATE_PREFIX = "Proofs.Generated.H1Aggregate"
LEAF_REL = Path("proofs/Proofs/Generated/H1Leaves")
OLEAN_REL = Path("proofs/.lake/build/lib/lean/Proofs/Generated/H1Leaves")
AGGREGATE_REL = Path("proofs/Proofs/Generated/H1Aggregate")
ADAPTER_REL = Path("proofs/Proofs/Generated/Erdos85OrderFortyNineOneHighCertificates.lean")
MATERIALIZER_REL = Path("h1fleet/materialize_replay_leaf_tree.py")
AGGREGATOR_REL = Path("research/problems/erdos-85-wip-01/sat49/generate_h1_v2_lean_aggregate.py")
ADAPTER_REL_PRODUCER = Path("research/problems/erdos-85-wip-01/sat49/generate_h1_post_aggregate_adapter.py")


class PipelineError(ValueError):
    pass


def canonical(value: object) -> bytes:
    return (json.dumps(value, ensure_ascii=True, allow_nan=False,
                       sort_keys=True, separators=(",", ":")) + "\n").encode("ascii")


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def safe(path: Path, label: str, kind: str = "file", absent: bool = False) -> None:
    if not path.is_absolute() or path != path.resolve(strict=False):
        raise PipelineError(f"{label} is not canonical absolute")
    current = path if path.exists() else path.parent
    while True:
        if current.is_symlink():
            raise PipelineError(f"{label} has symlink ancestry")
        if current == current.parent:
            break
        current = current.parent
    if absent:
        if path.exists() or path.is_symlink() or not path.parent.is_dir():
            raise PipelineError(f"{label} must be absent with an existing parent")
    elif kind == "file" and (path.is_symlink() or not path.is_file()):
        raise PipelineError(f"{label} is not a regular file")
    elif kind == "dir" and (path.is_symlink() or not path.is_dir()):
        raise PipelineError(f"{label} is not a directory")


def require(path: Path, label: str) -> dict[str, object]:
    safe(path, label)
    return {"bytes": path.stat().st_size, "path": str(path), "sha256": sha256_file(path)}


def read_canonical_json(path: Path, label: str, pretty: bool = False) -> dict:
    safe(path, label)
    raw = path.read_bytes()
    try:
        value = json.loads(raw)
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise PipelineError(f"{label} is malformed JSON") from error
    expected = ((json.dumps(value, sort_keys=True, indent=2) + "\n").encode()
                if pretty else canonical(value))
    if not isinstance(value, dict) or raw != expected:
        raise PipelineError(f"{label} is not canonical JSON")
    return value


def run(runner: Callable, kind: str, argv: list[str], cwd: Path) -> dict[str, object]:
    result = runner(kind, argv, cwd)
    if (not isinstance(result, dict) or set(result) != {"rc", "stdout", "stderr"}
            or type(result["rc"]) is not int
            or not isinstance(result["stdout"], bytes)
            or not isinstance(result["stderr"], bytes)):
        raise PipelineError(f"{kind} command result malformed")
    record = {
        "argv": argv, "cwd": str(cwd), "kind": kind, "rc": result["rc"],
        "stderr_bytes": len(result["stderr"]),
        "stderr_sha256": hashlib.sha256(result["stderr"]).hexdigest(),
        "stdout_bytes": len(result["stdout"]),
        "stdout_sha256": hashlib.sha256(result["stdout"]).hexdigest(),
    }
    if result["rc"] != 0:
        raise PipelineError(f"{kind} command failed rc={result['rc']}")
    return record


def tree_identity(root: Path, allowed_suffixes: tuple[str, ...], label: str) -> dict[str, object]:
    safe(root, label, kind="dir")
    rows: list[dict[str, object]] = []
    inodes: set[tuple[int, int]] = set()
    for current, dirs, files in os.walk(root, followlinks=False):
        base = Path(current)
        for name in dirs:
            if (base / name).is_symlink():
                raise PipelineError(f"{label} contains a directory symlink")
        for name in files:
            path = base / name
            if path.is_symlink() or not path.is_file():
                raise PipelineError(f"{label} contains a special file")
            relative = path.relative_to(root).as_posix()
            pure = PurePosixPath(relative)
            if any(part in ("", ".", "..") for part in pure.parts):
                raise PipelineError(f"{label} contains a malformed path")
            if not any(relative.endswith(suffix) for suffix in allowed_suffixes):
                raise PipelineError(f"{label} contains an unexpected file: {relative}")
            stat = path.stat()
            inode = (stat.st_dev, stat.st_ino)
            if stat.st_nlink != 1 or inode in inodes:
                raise PipelineError(f"{label} contains a hardlink/alias")
            inodes.add(inode)
            rows.append({"bytes": stat.st_size, "path": relative,
                         "sha256": sha256_file(path)})
    rows.sort(key=lambda row: row["path"])
    if not rows:
        raise PipelineError(f"{label} is empty")
    return {"bytes": sum(int(row["bytes"]) for row in rows),
            "file_count": len(rows),
            "identity_sha256": hashlib.sha256(canonical(rows)).hexdigest(),
            "root": str(root)}


def file_id(path: Path) -> dict[str, object]:
    return {"bytes": path.stat().st_size, "path": str(path), "sha256": sha256_file(path)}


def validate_materialized_contract(*, leaf_value: dict, evidence_value: dict,
        capacity_sha: str, manifest_sha: str, queue_sha: str,
        leaf_dir: Path, olean_dir: Path) -> None:
    modules, rows = leaf_value.get("modules"), evidence_value.get("rows")
    if (set(leaf_value) != {"capacity_index_sha256", "leaf_count", "modules", "schema"}
            or leaf_value.get("schema") != LEAF_INDEX_SCHEMA
            or leaf_value.get("capacity_index_sha256") != capacity_sha
            or leaf_value.get("leaf_count") != EXPECTED_LEAVES
            or not isinstance(modules, list) or len(modules) != EXPECTED_LEAVES
            or set(evidence_value) != {"capacity_index_sha256", "leaf_count", "manifest_sha256",
                "module_prefix", "profile_counts", "queue_sha256", "recompilable_from_tree",
                "rows", "schema"}
            or evidence_value.get("schema") != MATERIALIZATION_SCHEMA
            or evidence_value.get("capacity_index_sha256") != capacity_sha
            or evidence_value.get("manifest_sha256") != manifest_sha
            or evidence_value.get("queue_sha256") != queue_sha
            or evidence_value.get("profile_counts") != PROFILE_COUNTS
            or evidence_value.get("leaf_count") != EXPECTED_LEAVES
            or evidence_value.get("module_prefix") != LEAF_PREFIX
            or evidence_value.get("recompilable_from_tree") is not True
            or not isinstance(rows, list) or len(rows) != EXPECTED_LEAVES):
        raise PipelineError("materialized leaf/index contract mismatch")
    expected = [(profile, index) for profile, count in enumerate(PROFILE_COUNTS)
                for index in range(count)]
    tags: set[str] = set(); source_paths: set[Path] = set(); compact_paths: set[Path] = set(); olean_paths: set[Path] = set()
    for coordinate, module, row in zip(expected, modules, rows, strict=True):
        profile, local_index = coordinate
        if (not isinstance(module, dict) or set(module) != LEAF_FIELDS
                or not isinstance(row, dict) or set(row) != MATERIALIZATION_FIELDS):
            raise PipelineError("materialized ordered row schema mismatch")
        name = f"Erdos85H1V2CertP{profile}I{local_index:05d}"
        source = leaf_dir / f"{name}.lean"; compact = leaf_dir / f"{name}.compact.lrat"
        olean = olean_dir / f"{name}.olean"; source_module = f"{LEAF_PREFIX}.{name}"
        tag = row.get("orbit")
        if (not isinstance(tag, str) or not tag or tag in tags
                or (module.get("profile"), module.get("local_index"), module.get("orbit")) !=
                   (profile, local_index, tag)
                or (row.get("profile"), row.get("local_index"), row.get("module")) !=
                   (profile, local_index, source_module)
                or module.get("source_module") != source_module
                or module.get("source_path") != str(source) or row.get("source_path") != str(source)
                or row.get("compact_lrat_path") != str(compact) or row.get("olean_path") != str(olean)
                or row.get("source_sha256") != module.get("source_sha256")
                or row.get("source_bytes") != module.get("source_bytes")
                or row.get("recompilable_from_tree") is not True):
            raise PipelineError("materialized ordered row crosslink mismatch")
        tags.add(tag); source_paths.add(source); compact_paths.add(compact); olean_paths.add(olean)
        for path, bytes_key, sha_key in ((source, "source_bytes", "source_sha256"),
                                         (compact, "compact_lrat_bytes", "compact_lrat_sha256"),
                                         (olean, "olean_bytes", "olean_sha256")):
            safe(path, "materialized row output")
            if (type(row.get(bytes_key)) is not int or row[bytes_key] <= 0
                    or not isinstance(row.get(sha_key), str) or SHA256.fullmatch(row[sha_key]) is None
                    or path.stat().st_size != row[bytes_key] or sha256_file(path) != row[sha_key]):
                raise PipelineError("materialized row file identity mismatch")
    actual_leaf = {path for path in leaf_dir.iterdir() if path.is_file()}
    actual_olean = {path for path in olean_dir.iterdir() if path.is_file()}
    if actual_leaf != source_paths | compact_paths or actual_olean != olean_paths:
        raise PipelineError("materialized output file bijection mismatch")


def validate_layout_contract(value: dict, *, index: Path, inventory: Path,
                             aggregate_dir: Path) -> None:
    modules = value.get("modules")
    if (set(value) != LAYOUT_FIELDS or value.get("schema") != LAYOUT_SCHEMA
            or value.get("leaf_count") != EXPECTED_LEAVES
            or value.get("inputs") != {"index": file_id(index), "inventory": file_id(inventory)}
            or value.get("prefixes") != {"aggregate_modules": AGGREGATE_PREFIX,
                                         "leaf_modules": LEAF_PREFIX}
            or not isinstance(modules, list) or not modules):
        raise PipelineError("aggregate layout contract mismatch")
    files: set[Path] = set()
    for row in modules:
        if not isinstance(row, dict) or set(row) != LAYOUT_MODULE_FIELDS:
            raise PipelineError("aggregate layout row schema mismatch")
        path = aggregate_dir / str(row["file"])
        safe(path, "aggregate source")
        if (path.parent != aggregate_dir or path.suffix != ".lean" or path in files
                or path.stat().st_size != row["source_bytes"] or sha256_file(path) != row["source_sha256"]):
            raise PipelineError("aggregate layout/source identity mismatch")
        files.add(path)
    actual = {path for path in aggregate_dir.iterdir() if path.suffix == ".lean"}
    if actual != files:
        raise PipelineError("aggregate source file bijection mismatch")


def collect_outputs(*, adapter: Path, adapter_receipt: Path, aggregate_dir: Path,
                    leaf_index: Path, leaf_dir: Path, materialization_evidence: Path,
                    olean_dir: Path) -> dict[str, object]:
    return {"adapter_receipt": require(adapter_receipt, "adapter receipt"),
        "adapter_source": require(adapter, "adapter source"),
        "aggregate_tree": tree_identity(aggregate_dir, (".lean", ".json", ".sha256"), "aggregate tree"),
        "leaf_index": require(leaf_index, "leaf index"),
        "leaf_source_tree": tree_identity(leaf_dir, (".lean", ".compact.lrat"), "leaf source tree"),
        "materialization_evidence": require(materialization_evidence, "materialization evidence"),
        "olean_tree": tree_identity(olean_dir, (".olean",), "leaf olean tree")}


def build(*, repo: Path, source_commit: str, manifest: Path, queue: Path,
          capacity_index: Path, capacity_inventory: Path, reindex_receipt: Path,
          leaf_index: Path, materialization_evidence: Path, transcript: Path,
          object_store_root: Path | None, s3_bucket: str | None,
          aws: str, zstd: str, runner: Callable, before_transcript=None,
          transcript_writer=None, before_link=None, after_publish=None) -> dict[str, object]:
    safe(repo, "repo", kind="dir")
    if COMMIT.fullmatch(source_commit) is None:
        raise PipelineError("source commit malformed")
    if (object_store_root is None) == (s3_bucket is None):
        raise PipelineError("exactly one object-store backend is required")
    if object_store_root is not None:
        safe(object_store_root, "local object-store root", kind="dir")
    elif not isinstance(s3_bucket, str) or not s3_bucket:
        raise PipelineError("S3 bucket is malformed")
    inputs = [manifest, queue, capacity_index, capacity_inventory, reindex_receipt]
    producers = [Path(__file__).resolve(), repo / MATERIALIZER_REL,
                 repo / AGGREGATOR_REL, repo / ADAPTER_REL_PRODUCER]
    input_identities = [require(path, "pipeline input") for path in inputs]
    producer_identities = [require(path, "pipeline producer") for path in producers]
    python_identity = require(Path(sys.executable).resolve(), "Python executable")
    leaf_dir, olean_dir = repo / LEAF_REL, repo / OLEAN_REL
    aggregate_dir, adapter = repo / AGGREGATE_REL, repo / ADAPTER_REL
    adapter_receipt = Path(str(adapter) + ".receipt.json")
    for path, label in ((leaf_dir, "leaf source directory"), (olean_dir, "leaf olean directory"),
                        (aggregate_dir, "aggregate directory"), (adapter, "adapter source"),
                        (adapter_receipt, "adapter receipt"), (leaf_index, "leaf index"),
                        (materialization_evidence, "materialization evidence"),
                        (transcript, "pipeline transcript")):
        safe(path, label, absent=True)
    commands: list[dict[str, object]] = []
    commands.append(run(runner, "git_head", ["git", "rev-parse", "HEAD"], repo))
    head_result = runner("git_head_value", ["git", "rev-parse", "HEAD"], repo)
    if (set(head_result) != {"rc", "stdout", "stderr"} or head_result["rc"] != 0
            or head_result["stderr"] or head_result["stdout"].decode().strip() != source_commit):
        raise PipelineError("repo HEAD differs from reviewed source commit")
    clean = runner("git_status", ["git", "status", "--porcelain=v1", "--untracked-files=all"], repo)
    if set(clean) != {"rc", "stdout", "stderr"} or clean["rc"] != 0 or clean["stderr"] or clean["stdout"]:
        raise PipelineError("repo must be completely clean before materialization")
    materialize_argv = [sys.executable, str(producers[1]), "--manifest", str(manifest),
        "--queue", str(queue), "--capacity-index", str(capacity_index),
        "--capacity-reindex-receipt", str(reindex_receipt), "--source-dir", str(leaf_dir),
        "--olean-dir", str(olean_dir), "--leaf-index", str(leaf_index),
        "--evidence", str(materialization_evidence), "--module-prefix", LEAF_PREFIX]
    if object_store_root is not None:
        materialize_argv += ["--object-store-root", str(object_store_root)]
    else:
        materialize_argv += ["--s3-bucket", str(s3_bucket), "--aws", aws]
    materialize_argv += ["--zstd", zstd]
    commands.append(run(runner, "materialize", materialize_argv, repo))
    leaf_identity = require(leaf_index, "leaf index")
    materialization_identity = require(materialization_evidence, "materialization evidence")
    leaf_value = read_canonical_json(leaf_index, "leaf index")
    evidence_value = read_canonical_json(materialization_evidence, "materialization evidence")
    validate_materialized_contract(leaf_value=leaf_value, evidence_value=evidence_value,
        capacity_sha=str(input_identities[2]["sha256"]),
        manifest_sha=str(input_identities[0]["sha256"]), queue_sha=str(input_identities[1]["sha256"]),
        leaf_dir=leaf_dir, olean_dir=olean_dir)
    aggregate_argv = [sys.executable, str(producers[2]), "--index", str(capacity_index),
        "--inventory", str(capacity_inventory), "--stub-dir", str(leaf_dir),
        "--stub-module-prefix", LEAF_PREFIX, "--aggregate-module-prefix", AGGREGATE_PREFIX,
        "--bank-size", "128", "--output-dir", str(aggregate_dir)]
    commands.append(run(runner, "aggregate", aggregate_argv, repo))
    layout = aggregate_dir / "aggregate-layout.json"
    layout_identity = require(layout, "aggregate layout")
    layout_value = read_canonical_json(layout, "aggregate layout", pretty=True)
    validate_layout_contract(layout_value, index=capacity_index,
                             inventory=capacity_inventory, aggregate_dir=aggregate_dir)
    adapter_argv = [sys.executable, str(producers[3]), "--repo", str(repo),
        "--aggregate-layout", str(layout), "--aggregate-layout-sha256", str(layout_identity["sha256"]),
        "--aggregate-source-root", str(aggregate_dir), "--capacity-index", str(capacity_index),
        "--capacity-index-sha256", str(input_identities[2]["sha256"]),
        "--capacity-reindex-receipt", str(reindex_receipt),
        "--capacity-reindex-receipt-sha256", str(input_identities[4]["sha256"]),
        "--leaf-module-index", str(leaf_index), "--leaf-module-index-sha256", str(leaf_identity["sha256"]),
        "--output", str(adapter)]
    commands.append(run(runner, "adapter", adapter_argv, repo))
    adapter_value = read_canonical_json(adapter_receipt, "adapter receipt")
    if (set(adapter_value) != ADAPTER_FIELDS or adapter_value.get("schema") != ADAPTER_SCHEMA
            or adapter_value.get("leaf_count") != EXPECTED_LEAVES
            or adapter_value.get("leaf_module_index_sha256") != leaf_identity["sha256"]
            or adapter_value.get("aggregate_layout_sha256") != layout_identity["sha256"]
            or adapter_value.get("capacity_index_sha256") != input_identities[2]["sha256"]
            or adapter_value.get("capacity_reindex_receipt_sha256") != input_identities[4]["sha256"]
            or adapter_value.get("aggregate_layout_path") != str(layout)
            or adapter_value.get("leaf_module_index_path") != str(leaf_index)
            or adapter_value.get("capacity_index_path") != str(capacity_index)
            or adapter_value.get("capacity_reindex_receipt_path") != str(reindex_receipt)
            or adapter_value.get("aggregate_source_root") != str(aggregate_dir)
            or adapter_value.get("output_path") != str(adapter)
            or adapter_value.get("output_source_module") !=
                "Proofs.Generated.Erdos85OrderFortyNineOneHighCertificates"
            or adapter_value.get("output_bytes") != adapter.stat().st_size
            or adapter_value.get("output_sha256") != sha256_file(adapter)):
        raise PipelineError("adapter receipt contract mismatch")
    outputs = collect_outputs(adapter=adapter, adapter_receipt=adapter_receipt,
        aggregate_dir=aggregate_dir, leaf_index=leaf_index, leaf_dir=leaf_dir,
        materialization_evidence=materialization_evidence, olean_dir=olean_dir)
    final_head = runner("git_head_final", ["git", "rev-parse", "HEAD"], repo)
    tracked = runner("git_tracked_diff", ["git", "diff", "--quiet", "--ignore-submodules", "--"], repo)
    staged = runner("git_staged_diff", ["git", "diff", "--cached", "--quiet", "--ignore-submodules", "--"], repo)
    if (set(final_head) != {"rc", "stdout", "stderr"} or final_head["rc"] != 0 or final_head["stderr"]
            or final_head["stdout"].decode().strip() != source_commit
            or set(tracked) != {"rc", "stdout", "stderr"} or tracked["rc"] != 0 or tracked["stderr"]
            or set(staged) != {"rc", "stdout", "stderr"} or staged["rc"] != 0 or staged["stderr"]):
        raise PipelineError("tracked repository state drifted during create-only pipeline")
    for identity in [*input_identities, *producer_identities, python_identity]:
        if sha256_file(Path(str(identity["path"]))) != identity["sha256"]:
            raise PipelineError("pipeline input drift before transcript")
    if before_transcript:
        before_transcript()
    if collect_outputs(adapter=adapter, adapter_receipt=adapter_receipt,
            aggregate_dir=aggregate_dir, leaf_index=leaf_index, leaf_dir=leaf_dir,
            materialization_evidence=materialization_evidence, olean_dir=olean_dir) != outputs:
        raise PipelineError("pipeline output drift before transcript")
    value = {"commands": commands, "inputs": input_identities,
             "next_required_action": "human-review-and-commit-generated-lean-sources-only",
             "outputs": outputs, "producer_identities": producer_identities,
             "python_identity": python_identity, "repo": str(repo), "schema": SCHEMA,
             "source_commit": source_commit}
    raw = canonical(value)
    stage = transcript.with_name(f".{transcript.name}.stage.{os.getpid()}")
    safe(stage, "transcript stage", absent=True)
    published = False
    try:
        if transcript_writer is None:
            with stage.open("xb") as stream:
                stream.write(raw); stream.flush(); os.fsync(stream.fileno())
        else:
            transcript_writer(stage, raw)
        if not stage.is_file() or stage.is_symlink() or stage.read_bytes() != raw:
            raise PipelineError("staged transcript identity mismatch")
        if collect_outputs(adapter=adapter, adapter_receipt=adapter_receipt,
                aggregate_dir=aggregate_dir, leaf_index=leaf_index, leaf_dir=leaf_dir,
                materialization_evidence=materialization_evidence, olean_dir=olean_dir) != outputs:
            raise PipelineError("pipeline output drift during transcript publication")
        if before_link:
            before_link()
        os.link(stage, transcript)
        published = True
        if after_publish:
            after_publish()
        if transcript.read_bytes() != raw:
            raise PipelineError("published transcript identity mismatch")
        if collect_outputs(adapter=adapter, adapter_receipt=adapter_receipt,
                aggregate_dir=aggregate_dir, leaf_index=leaf_index, leaf_dir=leaf_dir,
                materialization_evidence=materialization_evidence, olean_dir=olean_dir) != outputs:
            raise PipelineError("pipeline output drift after transcript publication")
        fd = os.open(transcript.parent, os.O_RDONLY)
        try:
            os.fsync(fd)
        finally:
            os.close(fd)
    except BaseException:
        if published and transcript.exists() and os.path.samefile(stage, transcript):
            transcript.unlink()
        raise
    finally:
        stage.unlink(missing_ok=True)
    return value


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--source-commit", required=True)
    for name in ("manifest", "queue", "capacity-index", "capacity-inventory",
                 "capacity-reindex-receipt", "leaf-index", "materialization-evidence", "transcript"):
        parser.add_argument(f"--{name}", type=Path, required=True)
    backend = parser.add_mutually_exclusive_group(required=True)
    backend.add_argument("--object-store-root", type=Path)
    backend.add_argument("--s3-bucket")
    parser.add_argument("--aws", default="aws")
    parser.add_argument("--zstd", default="zstd")
    args = parser.parse_args()
    def runner(kind: str, argv: list[str], cwd: Path) -> dict[str, object]:
        result = subprocess.run(argv, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        return {"rc": result.returncode, "stdout": result.stdout, "stderr": result.stderr}
    try:
        build(repo=args.repo, source_commit=args.source_commit, manifest=args.manifest,
              queue=args.queue, capacity_index=args.capacity_index,
              capacity_inventory=args.capacity_inventory,
              reindex_receipt=args.capacity_reindex_receipt, leaf_index=args.leaf_index,
              materialization_evidence=args.materialization_evidence, transcript=args.transcript,
              object_store_root=args.object_store_root, s3_bucket=args.s3_bucket,
              aws=args.aws, zstd=args.zstd, runner=runner)
        print(f"WROTE {args.transcript}; STOP for human review/commit")
        return 0
    except (OSError, PipelineError, subprocess.SubprocessError) as error:
        print(f"PIPELINE_ERROR: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
