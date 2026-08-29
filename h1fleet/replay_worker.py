#!/usr/bin/env python3
"""Run one resumable, fail-closed H1 Lean replay transaction.

The worker deliberately supports a local object-store backend.  It exercises
the identical immutable-ready -> lifecycle-tag -> final-receipt state machine
without granting tests or preflight runs access to live S3.
"""

from __future__ import annotations

import argparse
import gzip
import json
import os
import re
import shutil
import subprocess
import sys
import time
import uuid
import tempfile
from dataclasses import replace
import urllib.error
import urllib.request
from pathlib import Path
from typing import Any

from replay_common import (
    READY_SCHEMA, RECEIPT_SCHEMA, AwsCliObjectStore, LocalObjectStore, ObjectStore,
    ReplayError,
    atomic_write, canonical_json, expand_command, info_record, load_json,
    load_manifest, require_sha, require_tag, run_command, sha256_bytes,
    sha256_file, validate_command_receipts,
)


def validate_job(job: dict[str, Any], tag_argument: str) -> dict[str, Any]:
    tag = require_tag(job.get("tag"))
    if tag != require_tag(tag_argument):
        raise ReplayError(f"job tag {tag} does not match requested tag {tag_argument}")
    for key in ("certificate_gzip_sha256", "compact_lrat_sha256", "cnf_sha256", "table_sha256"):
        require_sha(job.get(key), f"job.{key}")
    if type(job.get("profile")) is not int or job["profile"] not in range(5):
        raise ReplayError("job.profile must be in 0..4")
    if type(job.get("local_index")) is not int or job["local_index"] < 0:
        raise ReplayError("job.local_index must be a natural number")
    if not isinstance(job.get("certificate_key"), str) or not job["certificate_key"]:
        raise ReplayError("job.certificate_key must be nonempty")
    if not isinstance(job.get("table_serialization"), str) or not job["table_serialization"]:
        raise ReplayError("job.table_serialization must be a nonempty string")
    if sha256_bytes(job["table_serialization"].encode()) != job["table_sha256"]:
        raise ReplayError("job table serialization/hash mismatch")
    expected_key = f"sat49/campaign-20260825/h1/{tag}.compact.lrat.gz"
    if job["certificate_key"] != expected_key:
        raise ReplayError(f"certificate key must equal {expected_key}")
    return job


def validate_compact_lrat(path: Path) -> None:
    final_tokens: list[str] | None = None
    with path.open(errors="strict") as stream:
        for line_number, line in enumerate(stream, 1):
            tokens = line.split()
            if not tokens:
                continue
            try:
                [int(token) for token in tokens]
            except ValueError as error:
                raise ReplayError(f"compact LRAT line {line_number} is not integral") from error
            if tokens[-1] != "0":
                raise ReplayError(f"compact LRAT line {line_number} lacks terminal zero")
            final_tokens = tokens
    if final_tokens is None:
        raise ReplayError("compact LRAT is empty")
    if len(final_tokens) < 3 or final_tokens[1] != "0":
        raise ReplayError("compact LRAT does not end with an empty-clause addition")


def command_values(work: Path, job: dict[str, Any]) -> dict[str, str]:
    stem = f"h1V2P{job['profile']}I{job['local_index']:05d}"
    return {
        "tag": job["tag"], "profile": str(job["profile"]),
        "local_index": str(job["local_index"]), "stem": stem,
        "module": f"Erdos85H1V2CertP{job['profile']}I{job['local_index']:05d}",
        "work": str(work), "compact_lrat": str(work / "certificate.compact.lrat"),
        "source": str(work / "module.lean"), "olean": str(work / "module.olean"),
        "audit_json": str(work / "axiom-audit.json"),
        "log": str(work / "worker.log"),
    }


def receipt_command_bindings(work: Path, job: dict[str, Any]) -> dict[str, dict[str, str]]:
    values = command_values(work, job)
    result = {name: dict(values) for name in ("generate", "compile", "axiom_audit")}
    for label, input_name in (("source", "source"), ("olean", "olean"), ("log", "log")):
        result[f"zstd_{label}"] = dict(
            values, input=values[input_name], output=str(work / f"{label}.zst")
        )
    return result


def require_command_ok(name: str, command: list[str], work: Path, log: Path,
                       environment_allowlist: list[str]) -> dict[str, Any]:
    started = time.time()
    result = run_command(command, work, log, environment_allowlist)
    finished = time.time()
    if result.returncode != 0:
        raise ReplayError(f"{name} failed with rc={result.returncode}")
    return {
        "argv": result.argv, "returncode": result.returncode,
        "started_unix": started, "finished_unix": finished,
        "wall_seconds": finished - started,
        "user_cpu_seconds": result.user_cpu_seconds,
        "system_cpu_seconds": result.system_cpu_seconds,
        "peak_rss_kib": result.peak_rss_kib,
        "environment": result.environment,
        "stdout_sha256": sha256_bytes(result.stdout.encode()),
        "stderr_sha256": sha256_bytes(result.stderr.encode()),
    }


def validate_audit(path: Path, allowed: set[str], patterns: list[str],
                   native_axiom_prefix: str) -> dict[str, Any]:
    audit = load_json(path)
    if audit.get("schema") != "erdos85-h1-replay-axiom-audit-v1":
        raise ReplayError("axiom audit has wrong schema")
    if audit.get("sorry_ax") is not False or audit.get("source_scan") != "PASS":
        raise ReplayError("axiom audit does not prove sorry_ax=false and source scan PASS")
    axioms = audit.get("axioms")
    if not isinstance(axioms, list) or not all(isinstance(x, str) for x in axioms):
        raise ReplayError("axiom audit axioms must be a string list")
    compiled_patterns = [re.compile(pattern) for pattern in patterns]
    unexpected = sorted(
        axiom for axiom in set(axioms)
        if axiom not in allowed and not any(pattern.fullmatch(axiom) for pattern in compiled_patterns)
    )
    if unexpected:
        raise ReplayError(f"undisclosed axioms: {unexpected}")
    foreign_native = [
        axiom for axiom in axioms if axiom not in allowed
        and not axiom.startswith(native_axiom_prefix)
    ]
    if foreign_native:
        raise ReplayError(f"native axioms belong to another leaf: {foreign_native}")
    return audit


def artifact_key(prefix: str, kind: str, tag: str, suffix: str) -> str:
    return f"{prefix}{kind}/{tag}.{suffix}"


def ready_key(prefix: str, tag: str) -> str:
    return artifact_key(prefix, "replay-ready", tag, "json")


def receipt_key(prefix: str, tag: str) -> str:
    return artifact_key(prefix, "receipts", tag, "json")


def ledger_key(prefix: str, tag: str) -> str:
    return artifact_key(prefix, "ledger", tag, "accepted")


def try_load_remote_json(store: ObjectStore, key: str, destination: Path) -> dict[str, Any] | None:
    try:
        store.download(key, destination)
    except ReplayError as error:
        if str(error).startswith("missing object:"):
            return None
        raise
    return load_json(destination)


def validate_ready(ready: dict[str, Any], manifest: dict[str, Any], job: dict[str, Any],
                   store: ObjectStore) -> None:
    if ready.get("schema") != READY_SCHEMA or ready.get("tag") != job["tag"]:
        raise ReplayError("replay-ready identity mismatch")
    if ready.get("manifest_sha256") != manifest["manifest_sha256"]:
        raise ReplayError("replay-ready manifest mismatch")
    if ready.get("job_sha256") != job["job_sha256"]:
        raise ReplayError("replay-ready job mismatch")
    expected_job_identity = {
        "profile": job["profile"], "local_index": job["local_index"],
        "table_serialization": job["table_serialization"],
        "table_sha256": job["table_sha256"], "cnf_sha256": job["cnf_sha256"],
        "inventory_sha256": manifest["inventory_sha256"],
        "coverage_sha256": manifest["coverage_sha256"],
    }
    if ready.get("job_identity") != expected_job_identity:
        raise ReplayError("replay-ready inventory/table/CNF identity mismatch")
    expected_build_identity = {
        key: manifest[key] for key in (
            "repository_commit", "toolchain_identity", "overlay_sha256",
            "generator_sha256", "template_sha256", "cnf_emitter_sha256", "worker_sha256",
            "validator_sha256", "receipt_schema_sha256",
            "aggregate_generator_sha256", "axiom_auditor_sha256",
            "common_sha256", "dispatcher_sha256", "zstd_identity",
        )
    }
    if ready.get("build_identity") != expected_build_identity:
        raise ReplayError("replay-ready build identity mismatch")
    worker_runtime = ready.get("worker_runtime")
    if not isinstance(worker_runtime, dict) or not all(
        isinstance(worker_runtime.get(key), str) and worker_runtime[key]
        for key in ("instance_id", "availability_zone", "region", "instance_type",
                    "ami_id", "container_image_digest", "container_image_digest_source",
                    "identity_source")
    ):
        raise ReplayError("replay-ready worker runtime identity is malformed")
    if (
        worker_runtime["instance_type"] != manifest["worker_instance_type"]
        or worker_runtime["ami_id"] != manifest["worker_ami_id"]
        or worker_runtime["container_image_digest"] != manifest["worker_image_digest"]
        or (worker_runtime["region"] != manifest["aws_region"] and
            worker_runtime["identity_source"] != "local-test-backend")
    ):
        raise ReplayError("replay-ready worker runtime differs from manifest")
    local_runtime = worker_runtime["identity_source"] == "local-test-backend"
    if local_runtime:
        if worker_runtime["container_image_digest_source"] != "local-test-backend":
            raise ReplayError("local worker runtime source labels mismatch")
    elif (
        worker_runtime["identity_source"] != "aws-imdsv2-instance-identity-document"
        or worker_runtime["container_image_digest_source"]
        != "freight-manifest-assertion-bootstrap-verified"
        or re.fullmatch(re.escape(worker_runtime["region"]) + r"[a-z]",
                        worker_runtime["availability_zone"]) is None
    ):
        raise ReplayError("production worker runtime provenance is malformed")
    stem = f"h1V2P{job['profile']}I{job['local_index']:05d}"
    if ready.get("module") != {
        "name": f"Erdos85H1V2CertP{job['profile']}I{job['local_index']:05d}",
        "theorem": f"Erdos85.{stem}Checked",
    }:
        raise ReplayError("replay-ready module identity mismatch")
    compact = ready.get("compact_lrat")
    if (
        not isinstance(compact, dict)
        or compact.get("sha256") != job["compact_lrat_sha256"]
        or not isinstance(compact.get("size"), int)
        or compact["size"] <= 0
    ):
        raise ReplayError("replay-ready compact LRAT identity mismatch")
    for raw_name in ("source_raw", "olean_raw"):
        raw = ready.get(raw_name)
        if not isinstance(raw, dict) or not isinstance(raw.get("size"), int):
            raise ReplayError(f"replay-ready {raw_name} record is malformed")
        require_sha(raw.get("sha256"), f"replay-ready.{raw_name}.sha256")
    work_root = ready.get("work_root")
    if not isinstance(work_root, str) or work_root != str(Path(work_root).resolve()):
        raise ReplayError("replay-ready work root is not absolute and normalized")
    validate_command_receipts(
        ready.get("commands"), manifest.get("environment_allowlist", []),
        manifest["commands"], receipt_command_bindings(Path(work_root), job),
    )
    expected_native_prefix = (
        f"Erdos85.h1V2P{job['profile']}I{job['local_index']:05d}Check."
        "_native.native_decide.ax_"
    )
    if ready.get("native_axiom_prefix") != expected_native_prefix:
        raise ReplayError("replay-ready native axiom ownership mismatch")
    artifacts = ready.get("artifacts")
    if not isinstance(artifacts, dict) or set(artifacts) != {"source", "log", "olean"}:
        raise ReplayError("replay-ready artifact set mismatch")
    for label, expected in artifacts.items():
        if not isinstance(expected, dict):
            raise ReplayError(f"replay-ready {label} record is malformed")
        actual = store.head(expected.get("key", ""))
        if actual.sha256 != expected.get("sha256") or actual.size != expected.get("size"):
            raise ReplayError(f"replay-ready {label} read-back mismatch")
    expected_certificate = ready.get("certificate")
    if not isinstance(expected_certificate, dict):
        raise ReplayError("replay-ready certificate record is malformed")
    with tempfile.TemporaryDirectory() as temporary:
        actual = store.download(job["certificate_key"], Path(temporary) / "certificate")
    for field in ("key", "size", "sha256", "etag", "last_modified"):
        if getattr(actual, field) != expected_certificate.get(field):
            raise ReplayError(f"live certificate differs from replay-ready at {field}")
    if actual.version_id != expected_certificate.get("version_id"):
        raise ReplayError("live certificate differs from replay-ready at version_id")
    original_tags = expected_certificate.get("tags")
    if not isinstance(original_tags, dict):
        raise ReplayError("replay-ready certificate tags are malformed")
    allowed_tags = dict(original_tags, replay="consumed")
    if actual.tags not in (original_tags, allowed_tags):
        raise ReplayError("live certificate tags differ from replay-ready evidence")


def compile_ready(store: ObjectStore, manifest: dict[str, Any], job: dict[str, Any],
                  work: Path, worker_runtime: dict[str, str]) -> dict[str, Any]:
    values = command_values(work, job)
    log = Path(values["log"])
    atomic_write(log, b"")
    gzip_path = work / "certificate.compact.lrat.gz"
    certificate = store.download(job["certificate_key"], gzip_path)
    if certificate.sha256 != job["certificate_gzip_sha256"]:
        raise ReplayError("certificate gzip SHA-256 mismatch")
    if "replay" in certificate.tags:
        raise ReplayError("certificate already has a replay lifecycle tag without ready evidence")
    compact = Path(values["compact_lrat"])
    try:
        with gzip.open(gzip_path, "rb") as source, compact.open("wb") as destination:
            shutil.copyfileobj(source, destination)
    except (OSError, EOFError) as error:
        raise ReplayError(f"certificate gzip validation failed: {error}") from error
    if sha256_file(compact) != job["compact_lrat_sha256"]:
        raise ReplayError("decompressed compact LRAT SHA-256 mismatch")
    validate_compact_lrat(compact)

    commands = manifest["commands"]
    environment_allowlist = manifest.get("environment_allowlist", [])
    command_receipts = {
        "generate": require_command_ok(
            "generate", expand_command(commands["generate"], values), work, log,
            environment_allowlist),
    }
    source = Path(values["source"])
    if not source.is_file() or source.stat().st_size == 0:
        raise ReplayError("generator did not produce a nonempty Lean source")
    source_text = source.read_text()
    forbidden = re.compile(r"(?m)(?<![A-Za-z0-9_])(sorry|admit)(?![A-Za-z0-9_])")
    if forbidden.search(source_text):
        raise ReplayError("generated source contains sorry or admit")
    axiom_directive = f"\n#print axioms Erdos85.{values['stem']}Checked\n"
    if axiom_directive.strip() not in source_text:
        with source.open("a") as stream:
            stream.write(axiom_directive)
    command_receipts["compile"] = require_command_ok(
        "compile", expand_command(commands["compile"], values), work, log,
        environment_allowlist)
    olean = Path(values["olean"])
    if not olean.is_file() or olean.stat().st_size == 0:
        raise ReplayError("compiler did not produce a nonempty olean")
    command_receipts["axiom_audit"] = require_command_ok(
        "axiom_audit", expand_command(commands["axiom_audit"], values), work, log,
        environment_allowlist)
    native_axiom_prefix = (
        f"Erdos85.{values['stem']}Check._native.native_decide.ax_"
    )
    audit = validate_audit(
        Path(values["audit_json"]), set(manifest["allowed_axioms"]),
        manifest.get("allowed_axiom_patterns", []), native_axiom_prefix,
    )

    compressed: dict[str, Path] = {}
    for label, source_path in (("source", source), ("olean", olean), ("log", log)):
        destination = work / f"{label}.zst"
        zstd_values = dict(values, input=str(source_path), output=str(destination))
        command_receipts[f"zstd_{label}"] = require_command_ok(
            f"zstd_{label}", expand_command(commands["zstd"], zstd_values), work, log,
            environment_allowlist)
        if not destination.is_file() or destination.stat().st_size == 0:
            raise ReplayError(f"zstd did not produce {label} output")
        compressed[label] = destination

    prefix = manifest["campaign_prefix"]
    keys = {
        "source": artifact_key(prefix, "sources", job["tag"], "lean.zst"),
        "log": artifact_key(prefix, "logs", job["tag"], "log.zst"),
        "olean": artifact_key(prefix, "oleans", job["tag"], "olean.zst"),
    }
    metadata = {"tag": job["tag"], "manifest-sha256": manifest["manifest_sha256"]}
    artifacts = {
        label: info_record(store.put_immutable(keys[label], compressed[label], metadata))
        for label in ("source", "log", "olean")
    }
    ready = {
        "schema": READY_SCHEMA, "tag": job["tag"],
        "manifest_sha256": manifest["manifest_sha256"],
        "job_sha256": job["job_sha256"],
        "job_identity": {
            "profile": job["profile"], "local_index": job["local_index"],
            "table_serialization": job["table_serialization"],
            "table_sha256": job["table_sha256"], "cnf_sha256": job["cnf_sha256"],
            "inventory_sha256": manifest["inventory_sha256"],
            "coverage_sha256": manifest["coverage_sha256"],
        },
        "build_identity": {
            key: manifest[key] for key in (
                "repository_commit", "toolchain_identity", "overlay_sha256",
                "generator_sha256", "template_sha256", "cnf_emitter_sha256", "worker_sha256",
                "validator_sha256", "receipt_schema_sha256",
                "aggregate_generator_sha256", "axiom_auditor_sha256",
                "common_sha256", "dispatcher_sha256", "zstd_identity",
            )
        },
        "worker_runtime": worker_runtime,
        "module": {
            "name": values["module"], "theorem": f"Erdos85.{values['stem']}Checked",
        },
        "work_root": str(work),
        "certificate": info_record(certificate),
        "compact_lrat": {"size": compact.stat().st_size, "sha256": sha256_file(compact)},
        "source_raw": {"size": source.stat().st_size, "sha256": sha256_file(source)},
        "olean_raw": {"size": olean.stat().st_size, "sha256": sha256_file(olean)},
        "native_axiom_prefix": native_axiom_prefix,
        "axiom_audit": audit, "commands": command_receipts, "artifacts": artifacts,
    }
    store.put_bytes_immutable(
        ready_key(prefix, job["tag"]), canonical_json(ready), metadata)
    return ready


def finish_transaction(store: ObjectStore, manifest: dict[str, Any], job: dict[str, Any],
                       ready: dict[str, Any]) -> dict[str, Any]:
    validate_ready(ready, manifest, job, store)
    expected_before = ready["certificate"]
    with tempfile.TemporaryDirectory() as temporary:
        before = store.download(job["certificate_key"], Path(temporary) / "certificate-before")
    if before.tags.get("replay") == "consumed":
        after = before
        tagging_operation = "already_present"
        tagging_request_kind = "get-object-tagging-readback"
        tagging_request_id = before.tagging_request_id
    else:
        if before.tags != expected_before.get("tags"):
            raise ReplayError("certificate tags changed before lifecycle tagging")
        tagged = store.add_tag_preserving(job["certificate_key"], "replay", "consumed")
        with tempfile.TemporaryDirectory() as temporary:
            after = store.download(job["certificate_key"], Path(temporary) / "certificate-after")
        after = replace(after, tagging_request_id=tagged.tagging_request_id)
        tagging_operation = "performed"
        tagging_request_kind = "put-object-tagging"
        tagging_request_id = after.tagging_request_id
    if not tagging_request_id:
        raise ReplayError("lifecycle tagging lacks a request identifier")
    if after.tags.get("replay") != "consumed":
        raise ReplayError("consumed tag read-back failed")
    identity = ("etag", "size", "sha256", "last_modified", "version_id")
    if any(getattr(before, key) != getattr(after, key) for key in identity):
        raise ReplayError("certificate identity changed during lifecycle tagging")
    receipt = {
        "schema": RECEIPT_SCHEMA, "accepted": True, "tag": job["tag"],
        "manifest_sha256": manifest["manifest_sha256"],
        "job_sha256": job["job_sha256"],
        "replay_ready_sha256": sha256_bytes(canonical_json(ready)),
        "job_identity": ready["job_identity"],
        "build_identity": ready["build_identity"],
        "module": ready["module"],
        "certificate": ready["certificate"],
        "compact_lrat": ready["compact_lrat"],
        "source_raw": ready["source_raw"],
        "olean_raw": ready["olean_raw"],
        "commands": ready["commands"],
        "work_root": ready["work_root"],
        "worker_runtime": ready["worker_runtime"],
        "certificate_before_tagging": expected_before,
        "certificate_after_tagging": info_record(after),
        "tagging_operation": tagging_operation,
        "tagging_request_kind": tagging_request_kind,
        "tagging_request_id": tagging_request_id,
        "integrity": {
            "scheme": manifest["receipt_integrity_scheme"],
            "key_id": manifest["receipt_integrity_key_id"],
            "value": None,
        },
        "artifacts": ready["artifacts"], "axiom_audit": ready["axiom_audit"],
    }
    prefix = manifest["campaign_prefix"]
    ready_info = store.head(ready_key(prefix, job["tag"]))
    if ready_info.sha256 != receipt["replay_ready_sha256"]:
        raise ReplayError("immutable replay-ready object differs from validated record")
    receipt["replay_ready"] = info_record(ready_info)
    metadata = {"tag": job["tag"], "manifest-sha256": manifest["manifest_sha256"]}
    receipt_info = store.put_bytes_immutable(
        receipt_key(prefix, job["tag"]), canonical_json(receipt), metadata)
    ledger = {
        "schema": "erdos85-h1-replay-ledger-v1", "tag": job["tag"],
        "receipt_key": receipt_info.key, "receipt_sha256": receipt_info.sha256,
        "manifest_sha256": manifest["manifest_sha256"], "accepted": True,
    }
    store.put_bytes_immutable(ledger_key(prefix, job["tag"]), canonical_json(ledger), metadata)
    return receipt


def validate_existing_receipt(store: ObjectStore, manifest: dict[str, Any],
                              job: dict[str, Any], receipt: dict[str, Any],
                              work: Path) -> bool:
    if receipt.get("schema") != RECEIPT_SCHEMA or receipt.get("accepted") is not True:
        raise ReplayError("existing receipt is not validly accepted")
    if receipt.get("tag") != job["tag"]:
        raise ReplayError("existing receipt tag mismatch")
    if receipt.get("manifest_sha256") != manifest["manifest_sha256"]:
        raise ReplayError("existing receipt belongs to another manifest")
    if receipt.get("job_sha256") != job["job_sha256"]:
        raise ReplayError("existing receipt belongs to another job record")
    if not isinstance(receipt.get("tagging_request_id"), str) or not receipt["tagging_request_id"]:
        raise ReplayError("existing receipt lacks tagging request id")
    integrity = receipt.get("integrity")
    if not isinstance(integrity, dict) or (
        integrity.get("scheme") != manifest["receipt_integrity_scheme"]
        or integrity.get("key_id") != manifest["receipt_integrity_key_id"]
    ):
        raise ReplayError("existing receipt integrity declaration mismatch")
    if integrity["scheme"] != "local-test-unkeyed" and not isinstance(integrity.get("value"), str):
        raise ReplayError("existing receipt lacks keyed integrity evidence")
    prefix = manifest["campaign_prefix"]
    ready = try_load_remote_json(
        store, ready_key(prefix, job["tag"]), work / "accepted-ready.json"
    )
    if ready is None:
        raise ReplayError("accepted receipt lacks replay-ready record")
    validate_ready(ready, manifest, job, store)
    if receipt.get("replay_ready_sha256") != sha256_bytes(canonical_json(ready)):
        raise ReplayError("accepted receipt has wrong replay-ready hash")
    if receipt.get("artifacts") != ready.get("artifacts"):
        raise ReplayError("accepted receipt artifacts differ from replay-ready")
    if receipt.get("axiom_audit") != ready.get("axiom_audit"):
        raise ReplayError("accepted receipt audit differs from replay-ready")
    if receipt.get("certificate_before_tagging") != ready.get("certificate"):
        raise ReplayError("accepted receipt pre-tag identity differs from replay-ready")
    operation = receipt.get("tagging_operation")
    expected_kind = {
        "performed": "put-object-tagging",
        "already_present": "get-object-tagging-readback",
    }.get(operation)
    if expected_kind is None or receipt.get("tagging_request_kind") != expected_kind:
        raise ReplayError("accepted receipt tagging operation is malformed")
    after = receipt.get("certificate_after_tagging")
    if not isinstance(after, dict):
        raise ReplayError("accepted receipt lacks certificate tagging record")
    with tempfile.TemporaryDirectory() as temporary:
        certificate = store.download(
            job["certificate_key"], Path(temporary) / "accepted-certificate")
    if certificate.tags.get("replay") != "consumed":
        raise ReplayError("accepted certificate has lost replay=consumed")
    original_tags = ready["certificate"].get("tags")
    if not isinstance(original_tags, dict) or certificate.tags != dict(original_tags, replay="consumed"):
        raise ReplayError("accepted certificate tags differ from preserved ready evidence")
    if (certificate.etag, certificate.size, certificate.sha256, certificate.last_modified,
        certificate.version_id) != (
        after.get("etag"), after.get("size"), after.get("sha256"), after.get("last_modified"),
        after.get("version_id")
    ):
        raise ReplayError("accepted certificate identity no longer matches receipt")
    ledger = try_load_remote_json(
        store, ledger_key(prefix, job["tag"]), work / "accepted-ledger.json"
    )
    if ledger is None:
        return False
    receipt_info = store.head(receipt_key(prefix, job["tag"]))
    if ledger.get("accepted") is not True or ledger.get("tag") != job["tag"]:
        raise ReplayError("terminal ledger is malformed")
    if ledger.get("receipt_key") != receipt_info.key or ledger.get("receipt_sha256") != receipt_info.sha256:
        raise ReplayError("terminal ledger does not bind the live receipt")
    if ledger.get("manifest_sha256") != manifest["manifest_sha256"]:
        raise ReplayError("terminal ledger manifest mismatch")
    return True


def publish_ledger(store: ObjectStore, manifest: dict[str, Any], job: dict[str, Any]) -> None:
    prefix = manifest["campaign_prefix"]
    receipt_info = store.head(receipt_key(prefix, job["tag"]))
    if receipt_info.sha256 is None:
        raise ReplayError("receipt object lacks SHA-256 metadata")
    ledger = {
        "schema": "erdos85-h1-replay-ledger-v1", "tag": job["tag"],
        "receipt_key": receipt_info.key, "receipt_sha256": receipt_info.sha256,
        "manifest_sha256": manifest["manifest_sha256"], "accepted": True,
    }
    metadata = {"tag": job["tag"], "manifest-sha256": manifest["manifest_sha256"]}
    store.put_bytes_immutable(ledger_key(prefix, job["tag"]), canonical_json(ledger), metadata)


def validate_aws_cli(executable: str, expected_identity: str) -> None:
    version = subprocess.run(
        [executable, "--version"], text=True, capture_output=True, check=False)
    identity = (version.stdout + version.stderr).strip()
    if version.returncode != 0 or identity != expected_identity:
        raise ReplayError(
            f"AWS CLI identity mismatch: expected {expected_identity!r}, got {identity!r}")
    help_result = subprocess.run(
        [executable, "s3api", "put-object", "help"], text=True,
        capture_output=True, check=False, env=dict(os.environ, AWS_PAGER=""),
    )
    help_text = help_result.stdout + help_result.stderr
    if help_result.returncode != 0 or not all(
        option in help_text for option in ("--if-match", "--if-none-match")
    ):
        raise ReplayError("pinned AWS CLI lacks conditional put-object flags")


def load_imds_worker_runtime(manifest: dict[str, Any]) -> dict[str, str]:
    token_request = urllib.request.Request(
        "http://169.254.169.254/latest/api/token", method="PUT",
        headers={"X-aws-ec2-metadata-token-ttl-seconds": "60"},
    )
    try:
        with urllib.request.urlopen(token_request, timeout=2) as response:
            token = response.read().decode()
        identity_request = urllib.request.Request(
            "http://169.254.169.254/latest/dynamic/instance-identity/document",
            headers={"X-aws-ec2-metadata-token": token},
        )
        with urllib.request.urlopen(identity_request, timeout=2) as response:
            document = json.loads(response.read())
    except (OSError, urllib.error.URLError, json.JSONDecodeError) as error:
        raise ReplayError(f"cannot derive worker identity from IMDSv2: {error}") from error
    expected = {
        "instanceType": manifest["worker_instance_type"],
        "region": manifest["aws_region"],
        "imageId": manifest["worker_ami_id"],
    }
    if not isinstance(document, dict) or any(document.get(key) != value for key, value in expected.items()):
        raise ReplayError("IMDSv2 worker identity differs from frozen manifest")
    for key in ("instanceId", "availabilityZone"):
        if not isinstance(document.get(key), str) or not document[key]:
            raise ReplayError(f"IMDSv2 identity document lacks {key}")
    return {
        "instance_id": document["instanceId"],
        "availability_zone": document["availabilityZone"],
        "region": document["region"], "instance_type": document["instanceType"],
        "ami_id": document["imageId"],
        "container_image_digest": manifest["worker_image_digest"],
        "container_image_digest_source": "freight-manifest-assertion-bootstrap-verified",
        "identity_source": "aws-imdsv2-instance-identity-document",
    }


def validate_production_manifest(manifest: dict[str, Any]) -> None:
    placeholders = {"TBD", "TODO", "UNKNOWN", "UNRESOLVED"}
    launch_fields = (
        "repository_commit", "toolchain_identity", "zstd_identity", "aws_cli_identity",
        "worker_image_digest", "worker_ami_id", "worker_instance_type", "ebs_shape",
        "instance_role", "s3_bucket", "aws_region", "receipt_integrity_scheme",
        "receipt_integrity_key_id",
    )
    bad = [
        key for key in launch_fields
        if manifest[key].strip().upper() in placeholders
        or "local-test" in manifest[key].lower()
    ]
    hash_fields = (
        "inventory_sha256", "coverage_sha256", "overlay_sha256", "generator_sha256",
        "template_sha256", "cnf_emitter_sha256", "worker_sha256", "validator_sha256",
        "receipt_schema_sha256", "aggregate_generator_sha256", "axiom_auditor_sha256",
        "common_sha256", "dispatcher_sha256",
    )
    bad.extend(key for key in hash_fields if len(set(manifest[key])) == 1)
    formats = {
        "repository_commit": r"[0-9a-f]{40}",
        "worker_image_digest": r"[^@\s]+@sha256:[0-9a-f]{64}",
        "worker_ami_id": r"ami-[0-9a-f]+",
        "aws_region": r"[a-z]{2}-[a-z]+-[0-9]",
        "s3_bucket": r"[a-z0-9][a-z0-9.-]{1,61}[a-z0-9]",
    }
    bad.extend(key for key, pattern in formats.items() if re.fullmatch(pattern, manifest[key]) is None)
    if bad:
        raise ReplayError(f"production manifest contains unresolved or malformed identities: {sorted(set(bad))}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--job", type=Path, required=True)
    parser.add_argument("--tag", required=True)
    parser.add_argument("--state-dir", type=Path, required=True)
    backend = parser.add_mutually_exclusive_group(required=True)
    backend.add_argument("--object-store-root", type=Path,
                         help="local test/preflight object store")
    backend.add_argument("--s3-bucket", help="production S3 bucket (launch-gated)")
    parser.add_argument("--aws", default="aws", help="AWS CLI executable")
    args = parser.parse_args()
    try:
        manifest = load_manifest(args.manifest)
        manifest["manifest_sha256"] = sha256_file(args.manifest)
        job = validate_job(load_json(args.job), args.tag)
        job["job_sha256"] = sha256_file(args.job)
        tag = job["tag"]
        work = args.state_dir.resolve() / "work" / tag
        work.mkdir(parents=True, exist_ok=True)
        if args.object_store_root is not None:
            store: ObjectStore = LocalObjectStore(args.object_store_root)
            worker_runtime = {
                "instance_id": "local-test", "availability_zone": "local-test",
                "region": "local-test",
                "instance_type": manifest["worker_instance_type"],
                "ami_id": manifest["worker_ami_id"],
                "container_image_digest": manifest["worker_image_digest"],
                "container_image_digest_source": "local-test-backend",
                "identity_source": "local-test-backend",
            }
        else:
            validate_production_manifest(manifest)
            if args.s3_bucket != manifest["s3_bucket"]:
                raise ReplayError("S3 bucket differs from frozen manifest")
            if manifest["receipt_integrity_scheme"] in (
                "TBD", "local-test-unkeyed",
            ):
                raise ReplayError("editor-selected keyed receipt integrity is unresolved")
            raise ReplayError(
                f"unsupported receipt integrity scheme: {manifest['receipt_integrity_scheme']!r}")
            validate_aws_cli(args.aws, manifest["aws_cli_identity"])
            worker_runtime = load_imds_worker_runtime(manifest)
            store = AwsCliObjectStore(args.s3_bucket, args.aws)
        prefix = manifest["campaign_prefix"]

        claim_key = artifact_key(prefix, "claims", tag, "json")
        owner = str(uuid.uuid4())
        claim_token = store.acquire_claim(
            claim_key, owner, time.time(), manifest.get("claim_ttl_seconds", 86400))
        try:
            accepted = try_load_remote_json(store, receipt_key(prefix, tag), work / "existing-receipt.json")
            if accepted is not None:
                complete = validate_existing_receipt(store, manifest, job, accepted, work)
                if not complete:
                    publish_ledger(store, manifest, job)
                    print(f"RECOVERED_LEDGER tag={tag}")
                else:
                    print(f"ALREADY_ACCEPTED tag={tag}")
                return 0

            ready = try_load_remote_json(store, ready_key(prefix, tag), work / "existing-ready.json")
            if ready is None:
                ready = compile_ready(store, manifest, job, work, worker_runtime)
            receipt = finish_transaction(store, manifest, job, ready)
            atomic_write(work / "accepted-receipt.json", canonical_json(receipt))
            print(f"ACCEPTED tag={tag}")
            return 0
        finally:
            store.release_claim(claim_key, owner, claim_token, time.time())
    except ReplayError as error:
        print(f"REPLAY_ERROR: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
