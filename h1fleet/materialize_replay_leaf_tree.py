#!/usr/bin/env python3
"""Materialize an exact accepted replay census into canonical H1 leaf files."""

from __future__ import annotations

import argparse
import csv
import gzip
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any, Callable

from capacity_queue import (
    CAPACITY_PROFILE_COUNTS, PROFILE_NAMES, load_capacity_index,
    validate_queue_capacity, validate_queue_tables, validate_reindex_receipt,
)
from generate_replay_leaf import render as render_replay_leaf
from replay_common import (
    AwsCliObjectStore, LocalObjectStore, ObjectStore, ReplayError, atomic_write,
    canonical_json, load_json, load_manifest, sha256_bytes, sha256_file,
)
from replay_worker import artifact_key, receipt_key, validate_job
from validate_replay_receipt import (
    validate as validate_replay_receipt, validate_downloaded_identity,
)


SCHEMA = "erdos85-h1-replay-leaf-materialization-v1"
LEAF_INDEX_SCHEMA = "erdos85-h1-leaf-module-index-v1"
MODULE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)+")


def read_queue(path: Path, expected_sha256: str) -> list[dict[str, Any]]:
    if sha256_file(path) != expected_sha256:
        raise ReplayError("replay queue SHA-256 mismatch")
    jobs: list[dict[str, Any]] = []
    for number, line in enumerate(path.read_text().splitlines(), 1):
        if not line:
            raise ReplayError(f"queue line {number} is empty")
        try:
            value = json.loads(line)
        except json.JSONDecodeError as error:
            raise ReplayError(f"queue line {number} is malformed JSON") from error
        if not isinstance(value, dict) or canonical_json(value).decode().rstrip("\n") != line:
            raise ReplayError(f"queue line {number} is not canonical JSON")
        jobs.append(validate_job(value, str(value.get("tag", ""))))
    if len({job["tag"] for job in jobs}) != len(jobs):
        raise ReplayError("replay queue contains a duplicate tag")
    validate_queue_tables(jobs)
    return jobs


def read_capacity_rows(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    with path.open(newline="") as stream:
        reader = csv.DictReader(stream, delimiter="\t")
        required = {"orbit", "profile", "localIndex", "packed_lz4_sha256"}
        if not reader.fieldnames or not required.issubset(reader.fieldnames):
            raise ReplayError("capacity index lacks leaf materialization columns")
        for number, row in enumerate(reader, 2):
            try:
                profile = PROFILE_NAMES.index(row["profile"])
                local_index = int(row["localIndex"])
            except ValueError as error:
                raise ReplayError(f"capacity index line {number} has a malformed slot") from error
            packed = row["packed_lz4_sha256"]
            if re.fullmatch(r"[0-9a-f]{64}", packed) is None:
                raise ReplayError(f"capacity index line {number} has a malformed packed SHA")
            rows.append({"tag": row["orbit"], "profile": profile,
                         "local_index": local_index, "packed_sha256": packed})
    if [(row["profile"], row["local_index"]) for row in rows] != sorted(
        (row["profile"], row["local_index"]) for row in rows
    ):
        raise ReplayError("capacity index is not ordered by profile/local index")
    return rows


def decompress_zstd(executable: str, source: Path, destination: Path) -> None:
    with destination.open("xb") as output:
        result = subprocess.run(
            [executable, "-q", "-d", "-c", str(source)], stdout=output,
            stderr=subprocess.PIPE, check=False,
        )
    if result.returncode != 0:
        destination.unlink(missing_ok=True)
        raise ReplayError(f"zstd decompression failed rc={result.returncode}")


def require_raw(path: Path, identity: object, label: str) -> None:
    if not isinstance(identity, dict) or set(identity) != {"size", "sha256"}:
        raise ReplayError(f"{label} raw identity is malformed")
    if path.stat().st_size != identity["size"] or sha256_file(path) != identity["sha256"]:
        raise ReplayError(f"{label} raw identity mismatch")


def require_source_contract(source: bytes, tag: str, profile: int,
                            local_index: int, compact_lrat: Path) -> None:
    stem = f"h1V2P{profile}I{local_index:05d}"
    try:
        expected = render_replay_leaf(
            tag=tag, profile=profile, local_index=local_index,
            compact_lrat=compact_lrat,
        ) + f"\n#print axioms Erdos85.{stem}Checked\n"
    except ValueError as error:
        raise ReplayError(f"{tag}: cannot regenerate canonical source") from error
    if source != expected.encode():
        raise ReplayError(f"{tag}: source/module identity mismatch")


def select_exact_rows(rows: list[dict[str, Any]], jobs: list[dict[str, Any]],
                      capacity: dict[str, tuple[int, int]],
                      require_complete: bool) -> tuple[list[dict[str, Any]], dict[str, dict[str, Any]], list[int]]:
    validate_queue_capacity(jobs, capacity, require_complete)
    by_tag = {job["tag"]: job for job in jobs}
    if len(by_tag) != len(jobs):
        raise ReplayError("replay queue contains a duplicate tag")
    row_tags = [row["tag"] for row in rows]
    row_slots = [(row["profile"], row["local_index"]) for row in rows]
    if len(row_tags) != len(set(row_tags)) or len(row_slots) != len(set(row_slots)):
        raise ReplayError("capacity rows contain a duplicate tag or slot")
    selected = [row for row in rows if row["tag"] in by_tag]
    if len(selected) != len(jobs) or {row["tag"] for row in selected} != set(by_tag):
        raise ReplayError("capacity rows and replay queue are not a bijection")
    counts = [0] * 5
    for row in selected:
        job = by_tag[row["tag"]]
        if (job["profile"], job["local_index"]) != (row["profile"], row["local_index"]):
            raise ReplayError(f"{row['tag']}: valid tag is assigned to the wrong capacity slot")
        counts[row["profile"]] += 1
    if require_complete and tuple(counts) != CAPACITY_PROFILE_COUNTS:
        raise ReplayError("materialization does not cover all capacity profiles")
    return selected, by_tag, counts


def materialize(
    *, manifest_path: Path, queue_path: Path, capacity_index: Path,
    reindex_receipt: Path, source_dir: Path, olean_dir: Path,
    leaf_index_path: Path, evidence_path: Path, module_prefix: str,
    store: ObjectStore, zstd: str,
    validate_one: Callable[[argparse.Namespace], None],
    validator_backend: dict[str, Any], require_complete: bool = True,
) -> None:
    manifest = load_manifest(manifest_path)
    manifest_sha = sha256_file(manifest_path)
    if not MODULE.fullmatch(module_prefix):
        raise ReplayError("leaf module prefix is not a qualified Lean module")
    module_parts = tuple(module_prefix.split("."))
    if tuple(source_dir.parts[-len(module_parts):]) != module_parts:
        raise ReplayError("source directory does not match the canonical module prefix")
    if tuple(olean_dir.parts[-len(module_parts):]) != module_parts:
        raise ReplayError("olean directory does not match the canonical module prefix")
    if sha256_file(capacity_index) != manifest["capacity_index_sha256"]:
        raise ReplayError("capacity index differs from replay manifest")
    validate_reindex_receipt(
        reindex_receipt, capacity_index, str(manifest["inventory_sha256"])
    )
    if sha256_file(reindex_receipt) != manifest["capacity_reindex_receipt_sha256"]:
        raise ReplayError("capacity reindex receipt differs from replay manifest")
    capacity = load_capacity_index(capacity_index)
    rows = read_capacity_rows(capacity_index)
    jobs = read_queue(queue_path, str(manifest["queue_sha256"]))
    selected, by_tag, expected_counts = select_exact_rows(
        rows, jobs, capacity, require_complete,
    )

    outputs = (source_dir, olean_dir, leaf_index_path, evidence_path)
    resolved_outputs = [path.resolve() for path in outputs]
    if len(resolved_outputs) != len(set(resolved_outputs)):
        raise ReplayError("materialization outputs must be distinct")
    for file_output in (leaf_index_path, evidence_path):
        if source_dir in file_output.parents or olean_dir in file_output.parents:
            raise ReplayError("index/evidence outputs must be outside materialized trees")
    if any(path.exists() or path.is_symlink() for path in outputs):
        raise ReplayError("materialization outputs must be fresh")
    for path in outputs:
        if not path.is_absolute():
            raise ReplayError("materialization outputs must be absolute")
        path.parent.mkdir(parents=True, exist_ok=True)
    source_stage = Path(tempfile.mkdtemp(prefix=f".{source_dir.name}.stage.", dir=source_dir.parent))
    olean_stage = Path(tempfile.mkdtemp(prefix=f".{olean_dir.name}.stage.", dir=olean_dir.parent))
    index_stage = leaf_index_path.with_name(f".{leaf_index_path.name}.stage.{os.getpid()}")
    evidence_stage = evidence_path.with_name(f".{evidence_path.name}.stage.{os.getpid()}")
    leaf_rows: list[dict[str, Any]] = []
    evidence_rows: list[dict[str, Any]] = []
    published_source = False
    published_olean = False
    try:
        for row in selected:
            job = by_tag[row["tag"]]
            profile, local_index, tag = row["profile"], row["local_index"], row["tag"]
            if (job["profile"], job["local_index"]) != (profile, local_index):
                raise ReplayError(f"{tag}: valid tag is assigned to the wrong capacity slot")
            module_name = f"Erdos85H1V2CertP{profile}I{local_index:05d}"
            proof_name = f"{module_name}.compact.lrat"
            with tempfile.TemporaryDirectory() as raw:
                temporary = Path(raw)
                receipt_path = temporary / "receipt.json"
                store.download(receipt_key(manifest["campaign_prefix"], tag), receipt_path)
                validator_args = argparse.Namespace(
                    manifest=manifest_path, receipt=receipt_path, **validator_backend,
                )
                validate_one(validator_args)
                receipt = load_json(receipt_path)
                if receipt.get("job_sha256") != sha256_bytes(canonical_json(job)):
                    raise ReplayError(f"{tag}: accepted receipt does not bind the exact queue job")
                identity = receipt.get("job_identity")
                expected_identity = {
                    "profile": profile, "local_index": local_index,
                    "table_serialization": job["table_serialization"],
                    "table_sha256": job["table_sha256"], "cnf_sha256": job["cnf_sha256"],
                    "inventory_sha256": manifest["inventory_sha256"],
                    "coverage_sha256": manifest["coverage_sha256"],
                }
                if identity != expected_identity or receipt.get("tag") != tag:
                    raise ReplayError(f"{tag}: receipt job identity differs from queue")
                compact_identity = receipt.get("compact_lrat")
                if (not isinstance(compact_identity, dict)
                        or compact_identity.get("sha256") != job["compact_lrat_sha256"]):
                    raise ReplayError(f"{tag}: receipt compact LRAT differs from queue")
                if receipt.get("module") != {
                    "name": module_name, "theorem": f"Erdos85.h1V2P{profile}I{local_index:05d}Checked",
                }:
                    raise ReplayError(f"{tag}: receipt module identity mismatch")
                artifacts = receipt["artifacts"]
                source_zst, olean_zst = temporary / "source.zst", temporary / "olean.zst"
                source_info = store.download(artifacts["source"]["key"], source_zst)
                olean_info = store.download(artifacts["olean"]["key"], olean_zst)
                validate_downloaded_identity(
                    f"{tag} source", artifacts["source"], source_info, source_zst,
                )
                validate_downloaded_identity(
                    f"{tag} olean", artifacts["olean"], olean_info, olean_zst,
                )
                source_raw, olean_raw = temporary / "source.lean", temporary / "source.olean"
                decompress_zstd(zstd, source_zst, source_raw)
                decompress_zstd(zstd, olean_zst, olean_raw)
                require_raw(source_raw, receipt.get("source_raw"), f"{tag} source")
                require_raw(olean_raw, receipt.get("olean_raw"), f"{tag} olean")
                certificate_gzip = temporary / "certificate.gz"
                certificate_info = store.download(job["certificate_key"], certificate_gzip)
                if sha256_file(certificate_gzip) != job["certificate_gzip_sha256"]:
                    raise ReplayError(f"{tag}: certificate gzip identity mismatch")
                validate_downloaded_identity(
                    f"{tag} certificate", receipt.get("certificate_after_tagging"),
                    certificate_info, certificate_gzip,
                )
                compact = source_stage / proof_name
                with gzip.open(certificate_gzip, "rb") as compressed, compact.open("xb") as output:
                    shutil.copyfileobj(compressed, output)
                require_raw(compact, compact_identity, f"{tag} compact LRAT")
                if sha256_file(compact) != job["compact_lrat_sha256"]:
                    raise ReplayError(f"{tag}: restored compact LRAT identity mismatch")
                require_source_contract(
                    source_raw.read_bytes(), tag, profile, local_index, compact,
                )
                source_output = source_stage / f"{module_name}.lean"
                olean_output = olean_stage / f"{module_name}.olean"
                atomic_write(source_output, source_raw.read_bytes())
                atomic_write(olean_output, olean_raw.read_bytes())
                final_source = source_dir / source_output.name
                final_olean = olean_dir / olean_output.name
                source_module = f"{module_prefix}.{module_name}"
                leaf_rows.append({
                    "local_index": local_index, "orbit": tag,
                    "packed_lrat_sha256": row["packed_sha256"], "profile": profile,
                    "source_bytes": source_output.stat().st_size,
                    "source_module": source_module, "source_path": str(final_source),
                    "source_sha256": sha256_file(source_output),
                })
                evidence_rows.append({
                    "certificate_gzip_bytes": certificate_gzip.stat().st_size,
                    "certificate_gzip_sha256": job["certificate_gzip_sha256"],
                    "certificate_key": job["certificate_key"],
                    "compact_lrat_bytes": compact.stat().st_size,
                    "compact_lrat_path": str(source_dir / proof_name),
                    "compact_lrat_sha256": job["compact_lrat_sha256"],
                    "local_index": local_index, "module": source_module,
                    "olean_artifact_key": artifacts["olean"]["key"],
                    "olean_bytes": olean_output.stat().st_size,
                    "olean_path": str(final_olean), "olean_sha256": sha256_file(olean_output),
                    "orbit": tag, "profile": profile,
                    "recompilable_from_tree": True,
                    "replay_ready_key": receipt["replay_ready"]["key"],
                    "replay_ready_sha256": receipt["replay_ready_sha256"],
                    "receipt_key": receipt_key(manifest["campaign_prefix"], tag),
                    "receipt_sha256": sha256_file(receipt_path),
                    "source_artifact_key": artifacts["source"]["key"],
                    "source_bytes": source_output.stat().st_size,
                    "source_path": str(final_source), "source_sha256": sha256_file(source_output),
                    "theorem": f"Erdos85.h1V2P{profile}I{local_index:05d}Checked",
                })
        index = {"capacity_index_sha256": sha256_file(capacity_index),
                 "leaf_count": len(leaf_rows), "modules": leaf_rows,
                 "schema": LEAF_INDEX_SCHEMA}
        evidence = {"capacity_index_sha256": sha256_file(capacity_index),
                    "leaf_count": len(evidence_rows), "manifest_sha256": manifest_sha,
                    "module_prefix": module_prefix, "profile_counts": expected_counts,
                    "recompilable_from_tree": True,
                    "queue_sha256": sha256_file(queue_path), "rows": evidence_rows,
                    "schema": SCHEMA}
        atomic_write(index_stage, canonical_json(index))
        atomic_write(evidence_stage, canonical_json(evidence))
        os.rename(source_stage, source_dir)
        published_source = True
        os.rename(olean_stage, olean_dir)
        published_olean = True
        os.link(index_stage, leaf_index_path)
        os.link(evidence_stage, evidence_path)
    except BaseException:
        shutil.rmtree(source_stage, ignore_errors=True)
        shutil.rmtree(olean_stage, ignore_errors=True)
        if published_source: shutil.rmtree(source_dir)
        if published_olean: shutil.rmtree(olean_dir)
        leaf_index_path.unlink(missing_ok=True)
        evidence_path.unlink(missing_ok=True)
        raise
    finally:
        index_stage.unlink(missing_ok=True)
        evidence_stage.unlink(missing_ok=True)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--queue", type=Path, required=True)
    parser.add_argument("--capacity-index", type=Path, required=True)
    parser.add_argument("--capacity-reindex-receipt", type=Path, required=True)
    parser.add_argument("--source-dir", type=Path, required=True)
    parser.add_argument("--olean-dir", type=Path, required=True)
    parser.add_argument("--leaf-index", type=Path, required=True)
    parser.add_argument("--evidence", type=Path, required=True)
    parser.add_argument("--module-prefix", required=True)
    backend = parser.add_mutually_exclusive_group(required=True)
    backend.add_argument("--object-store-root", type=Path)
    backend.add_argument("--s3-bucket")
    parser.add_argument("--aws", default="aws")
    parser.add_argument("--zstd", default="zstd")
    args = parser.parse_args()
    try:
        if args.object_store_root is not None:
            store: ObjectStore = LocalObjectStore(args.object_store_root)
        else:
            store = AwsCliObjectStore(args.s3_bucket, args.aws)
        materialize(
            manifest_path=args.manifest, queue_path=args.queue,
            capacity_index=args.capacity_index,
            reindex_receipt=args.capacity_reindex_receipt,
            source_dir=args.source_dir, olean_dir=args.olean_dir,
            leaf_index_path=args.leaf_index, evidence_path=args.evidence,
            module_prefix=args.module_prefix, store=store, zstd=args.zstd,
            validate_one=validate_replay_receipt,
            validator_backend={"object_store_root": args.object_store_root,
                               "s3_bucket": args.s3_bucket, "aws": args.aws},
        )
    except (OSError, ValueError, ReplayError, subprocess.SubprocessError) as error:
        print(f"INVALID: {error}", file=sys.stderr)
        return 2
    print(f"WROTE {args.leaf_index} leaves={sum(CAPACITY_PROFILE_COUNTS)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
