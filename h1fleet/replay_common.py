#!/usr/bin/env python3
"""Shared, fail-closed primitives for the H1 Lean replay stage."""

from __future__ import annotations

import copy
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
import uuid
import string
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Protocol


TAG_RE = re.compile(r"[0-9a-f]{16}")
SHA_RE = re.compile(r"[0-9a-f]{64}")
SCHEMA = "erdos85-h1-replay-manifest-v2"
READY_SCHEMA = "erdos85-h1-replay-ready-v2"
RECEIPT_SCHEMA = "erdos85-h1-replay-receipt-v2"
NATIVE_AXIOM_PATTERN = (
    r"^Erdos85\.h1V2P[0-4]I[0-9]{5}Check\._native\.native_decide\.ax_[0-9_]+$"
)
FOUNDATIONAL_AXIOMS = ("propext", "Classical.choice", "Quot.sound")
RECEIPT_INTEGRITY_SCHEME = "canonical-json-sha256-v1"
RECEIPT_FIELDS = {
    "schema", "accepted", "tag", "manifest_sha256", "job_sha256",
    "replay_ready_sha256", "job_identity", "build_identity", "module",
    "certificate", "compact_lrat", "source_raw", "olean_raw", "commands",
    "work_root", "worker_runtime", "certificate_before_tagging",
    "certificate_after_tagging", "tagging_operation", "tagging_request_kind",
    "tagging_request_id", "integrity", "artifacts", "axiom_audit",
    "replay_ready",
}


class ReplayError(RuntimeError):
    """A fail-closed replay validation or transaction failure."""


def canonical_json(value: Any) -> bytes:
    def reject_floats(item: Any) -> None:
        if isinstance(item, float):
            raise ReplayError("canonical JSON contract forbids floats")
        if isinstance(item, dict):
            for key, child in item.items():
                if not isinstance(key, str):
                    raise ReplayError("canonical JSON object keys must be strings")
                reject_floats(child)
        elif isinstance(item, (list, tuple)):
            for child in item:
                reject_floats(child)

    reject_floats(value)
    try:
        encoded = json.dumps(
            value, sort_keys=True, separators=(",", ":"), allow_nan=False)
    except (TypeError, ValueError) as error:
        raise ReplayError(f"value is not canonical JSON: {error}") from error
    return (encoded + "\n").encode()


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def receipt_integrity_sha256(receipt: dict[str, Any]) -> str:
    """Hash the exact canonical receipt with its self-hash field omitted."""
    candidate = copy.deepcopy(receipt)
    validate_receipt_fields(candidate)
    integrity = candidate.get("integrity")
    if not isinstance(integrity, dict) or set(integrity) != {"scheme", "receipt_sha256"}:
        raise ReplayError("receipt integrity declaration is malformed")
    if integrity.get("scheme") != RECEIPT_INTEGRITY_SCHEME:
        raise ReplayError("receipt integrity contract mismatch")
    del integrity["receipt_sha256"]
    return sha256_bytes(canonical_json(candidate))


def validate_receipt_fields(receipt: dict[str, Any]) -> None:
    if set(receipt) != RECEIPT_FIELDS:
        raise ReplayError("receipt fields differ from exact schema")


def seal_receipt_integrity(receipt: dict[str, Any]) -> None:
    integrity = receipt.get("integrity")
    if not isinstance(integrity, dict):
        raise ReplayError("receipt integrity declaration is malformed")
    integrity["receipt_sha256"] = receipt_integrity_sha256(receipt)


def validate_receipt_integrity(receipt: dict[str, Any]) -> None:
    integrity = receipt.get("integrity")
    if not isinstance(integrity, dict) or not isinstance(integrity.get("receipt_sha256"), str):
        raise ReplayError("receipt lacks canonical SHA-256 integrity evidence")
    require_sha(integrity["receipt_sha256"], "receipt.integrity.receipt_sha256")
    if integrity["receipt_sha256"] != receipt_integrity_sha256(receipt):
        raise ReplayError("receipt canonical SHA-256 integrity mismatch")


def atomic_write(path: Path, value: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    handle, temporary_name = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    temporary = Path(temporary_name)
    try:
        with os.fdopen(handle, "wb") as stream:
            stream.write(value)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
    except BaseException:
        temporary.unlink(missing_ok=True)
        raise


def require_sha(value: Any, label: str) -> str:
    if not isinstance(value, str) or not SHA_RE.fullmatch(value):
        raise ReplayError(f"{label} must be a lowercase SHA-256")
    return value


def require_tag(value: Any) -> str:
    if not isinstance(value, str) or not TAG_RE.fullmatch(value):
        raise ReplayError("tag must be 16 lowercase hexadecimal characters")
    return value


def load_json(path: Path) -> dict[str, Any]:
    def exact_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, item in pairs:
            if key in result:
                raise ReplayError(f"duplicate JSON key {key!r}")
            result[key] = item
        return result

    def reject_float(value: str) -> Any:
        raise ReplayError(f"JSON floats are forbidden: {value}")

    try:
        value = json.loads(
            path.read_text(), object_pairs_hook=exact_object, parse_float=reject_float,
        )
    except (OSError, json.JSONDecodeError, ReplayError) as error:
        raise ReplayError(f"cannot read JSON {path}: {error}") from error
    if not isinstance(value, dict):
        raise ReplayError(f"{path}: top-level JSON must be an object")
    return value


def load_manifest(path: Path) -> dict[str, Any]:
    value = load_json(path)
    required_strings = (
        "schema", "campaign_prefix", "repository_commit", "inventory_sha256",
        "coverage_sha256", "toolchain_identity", "overlay_sha256",
        "generator_sha256", "template_sha256", "cnf_emitter_sha256", "worker_sha256",
        "validator_sha256", "zstd_identity",
        "receipt_schema_sha256", "aggregate_generator_sha256",
        "stub_generator_sha256", "capacity_exporter_sha256",
        "capacity_reindexer_sha256", "capacity_queue_validator_sha256",
        "capacity_index_sha256", "capacity_reindex_receipt_sha256",
        "axiom_auditor_sha256", "common_sha256", "dispatcher_sha256",
        "aws_cli_identity",
        "worker_image_digest", "worker_ami_id", "worker_instance_type", "ebs_shape",
        "instance_role", "s3_bucket",
        "aws_region",
        "receipt_integrity_scheme", "single_writer_lock_path",
        "queue_sha256",
    )
    missing = [
        key for key in required_strings
        if not isinstance(value.get(key), str) or not value[key].strip()
    ]
    if missing:
        raise ReplayError(f"manifest missing string fields: {missing}")
    if value["schema"] != SCHEMA:
        raise ReplayError(f"unsupported manifest schema: {value['schema']!r}")
    for key in (
        "inventory_sha256", "coverage_sha256", "overlay_sha256",
        "generator_sha256", "template_sha256", "cnf_emitter_sha256", "worker_sha256",
        "validator_sha256",
        "receipt_schema_sha256", "aggregate_generator_sha256",
        "stub_generator_sha256", "capacity_exporter_sha256",
        "capacity_reindexer_sha256", "capacity_queue_validator_sha256",
        "capacity_index_sha256", "capacity_reindex_receipt_sha256",
        "axiom_auditor_sha256", "common_sha256", "dispatcher_sha256",
        "queue_sha256",
    ):
        require_sha(value[key], f"manifest.{key}")
    expected_jobs = value.get("expected_jobs")
    if type(expected_jobs) is not int or expected_jobs <= 0:
        raise ReplayError("manifest.expected_jobs must be a positive integer")
    maximum_parallelism = value.get("max_parallelism")
    if type(maximum_parallelism) is not int or maximum_parallelism <= 0:
        raise ReplayError("manifest.max_parallelism must be a positive integer")
    if value.get("single_dispatcher") is not True:
        raise ReplayError("manifest.single_dispatcher must be true")
    if (
        value["receipt_integrity_scheme"] != RECEIPT_INTEGRITY_SCHEME
    ):
        raise ReplayError("manifest receipt integrity contract must be canonical JSON SHA-256")
    lock_path = Path(value["single_writer_lock_path"])
    if not lock_path.is_absolute() or lock_path != lock_path.resolve():
        raise ReplayError("manifest.single_writer_lock_path must be absolute and normalized")
    if type(value.get("complete_capacity_queue")) is not bool:
        raise ReplayError("manifest.complete_capacity_queue must be boolean")
    prefix = value["campaign_prefix"]
    if prefix.startswith("/") or ".." in prefix.split("/") or not prefix.endswith("/"):
        raise ReplayError("campaign_prefix must be normalized, relative, and end in /")
    commands = value.get("commands")
    if not isinstance(commands, dict):
        raise ReplayError("manifest.commands must be an object")
    for name in ("generate", "compile", "axiom_audit", "zstd"):
        command = commands.get(name)
        if not isinstance(command, list) or not command or not all(isinstance(x, str) for x in command):
            raise ReplayError(f"manifest.commands.{name} must be a nonempty string list")
        if not Path(command[0]).is_absolute():
            raise ReplayError(f"manifest.commands.{name} executable must be absolute")
    allowed = value.get("allowed_axioms")
    if allowed != list(FOUNDATIONAL_AXIOMS):
        raise ReplayError(
            "manifest.allowed_axioms must equal the canonical foundational list"
        )
    patterns = value.get("allowed_axiom_patterns", [])
    if patterns not in ([], [NATIVE_AXIOM_PATTERN]):
        raise ReplayError(
            "manifest.allowed_axiom_patterns must be empty or the singleton "
            "reviewed native leaf-root pattern"
        )
    for pattern in patterns:
        try:
            re.compile(pattern)
        except re.error as error:
            raise ReplayError(f"invalid axiom pattern {pattern!r}: {error}") from error
    environment = value.get("environment_allowlist", [])
    if not isinstance(environment, list) or not all(
        isinstance(name, str) and re.fullmatch(r"[A-Z][A-Z0-9_]{0,127}", name)
        for name in environment
    ):
        raise ReplayError("manifest.environment_allowlist must be an uppercase variable-name list")
    if len(environment) != len(set(environment)):
        raise ReplayError("manifest.environment_allowlist must not contain duplicates")
    if "claim_ttl_seconds" in value or "receipt_integrity_key_id" in value:
        raise ReplayError("manifest contains obsolete lease or keyed-integrity fields")
    return value


def expand_command(command: list[str], values: dict[str, str]) -> list[str]:
    result = []
    for argument in command:
        try:
            expanded = argument.format_map(values)
        except KeyError as error:
            raise ReplayError(f"unknown command placeholder {error.args[0]!r}") from error
        if "{" in expanded or "}" in expanded:
            raise ReplayError(f"unexpanded command placeholder in {expanded!r}")
        result.append(expanded)
    return result


def _argv_matches_template(argv: list[str], template: list[str],
                           expected_bindings: dict[str, str] | None = None) -> bool:
    if len(argv) != len(template):
        return False
    formatter = string.Formatter()
    bindings: dict[str, str] = dict(expected_bindings or {})
    for actual, expected in zip(argv, template):
        pattern = ""
        argument_fields: set[str] = set()
        try:
            for literal, field, format_spec, conversion in formatter.parse(expected):
                pattern += re.escape(literal)
                if field is not None:
                    if format_spec or conversion:
                        return False
                    if field in bindings:
                        pattern += re.escape(bindings[field])
                    elif field in argument_fields:
                        pattern += f"(?P={field})"
                    else:
                        pattern += f"(?P<{field}>.+)"
                        argument_fields.add(field)
        except ValueError:
            return False
        match = re.fullmatch(pattern, actual)
        if match is None:
            return False
        bindings.update({key: value for key, value in match.groupdict().items() if value is not None})
    return True


def validate_command_receipts(receipts: Any, environment_allowlist: list[str],
                              command_templates: dict[str, list[str]] | None = None,
                              command_bindings: dict[str, dict[str, str]] | None = None) -> None:
    expected = {"generate", "compile", "axiom_audit", "zstd_source", "zstd_log", "zstd_olean"}
    if not isinstance(receipts, dict) or set(receipts) != expected:
        raise ReplayError("command receipt set mismatch")
    allowed_environment = set(environment_allowlist)
    for name, receipt in receipts.items():
        if not isinstance(receipt, dict) or receipt.get("returncode") != 0:
            raise ReplayError(f"command receipt {name} is not successful")
        expected_fields = {
            "argv", "returncode", "started_unix_ns", "finished_unix_ns", "wall_ns",
            "user_cpu_ns", "system_cpu_ns", "peak_rss_kib", "environment",
            "stdout_sha256", "stderr_sha256",
        }
        if set(receipt) != expected_fields:
            raise ReplayError(f"command receipt {name} fields differ from exact schema")
        if not isinstance(receipt.get("argv"), list) or not receipt["argv"] or not all(
            isinstance(argument, str) for argument in receipt["argv"]
        ):
            raise ReplayError(f"command receipt {name} argv is malformed")
        if command_templates is not None:
            template_name = "zstd" if name.startswith("zstd_") else name
            template = command_templates.get(template_name)
            bindings = None if command_bindings is None else command_bindings.get(name)
            if not isinstance(template, list) or not _argv_matches_template(
                receipt["argv"], template, bindings
            ):
                raise ReplayError(f"command receipt {name} argv differs from manifest template")
        for field in ("started_unix_ns", "finished_unix_ns", "wall_ns",
                      "user_cpu_ns", "system_cpu_ns"):
            value = receipt.get(field)
            if type(value) is not int or value < 0:
                raise ReplayError(f"command receipt {name}.{field} is malformed")
        if receipt["finished_unix_ns"] < receipt["started_unix_ns"]:
            raise ReplayError(f"command receipt {name} timestamps are reversed")
        delta = receipt["finished_unix_ns"] - receipt["started_unix_ns"]
        if receipt["wall_ns"] != delta:
            raise ReplayError(f"command receipt {name}.wall_ns disagrees with timestamps")
        if (isinstance(receipt.get("peak_rss_kib"), bool)
                or not isinstance(receipt.get("peak_rss_kib"), int)
                or receipt["peak_rss_kib"] <= 0):
            raise ReplayError(f"command receipt {name}.peak_rss_kib is malformed")
        for field in ("stdout_sha256", "stderr_sha256"):
            require_sha(receipt.get(field), f"command receipt {name}.{field}")
        environment = receipt.get("environment")
        if not isinstance(environment, dict) or set(environment) != allowed_environment:
            raise ReplayError(f"command receipt {name} environment does not record the exact allowlist")
        if not all(isinstance(key, str) and (value is None or isinstance(value, str))
                   for key, value in environment.items()):
            raise ReplayError(f"command receipt {name} environment is malformed")


@dataclass(frozen=True)
class CommandResult:
    argv: list[str]
    returncode: int
    stdout: str
    stderr: str
    user_cpu_seconds: float
    system_cpu_seconds: float
    peak_rss_kib: int
    environment: dict[str, str | None]


def run_command(command: list[str], cwd: Path, log: Path,
                environment_allowlist: list[str] | None = None) -> CommandResult:
    recorded_environment = {
        key: os.environ.get(key) for key in (environment_allowlist or [])
    }
    child_environment = {
        key: value for key, value in recorded_environment.items() if value is not None
    }
    with tempfile.TemporaryDirectory() as temporary:
        stdout_path = Path(temporary) / "stdout"
        stderr_path = Path(temporary) / "stderr"
        with stdout_path.open("wb") as stdout_stream, stderr_path.open("wb") as stderr_stream:
            process = subprocess.Popen(
                command, cwd=cwd, stdout=stdout_stream, stderr=stderr_stream,
                env=child_environment,
            )
            _, status, usage = os.wait4(process.pid, 0)
            process.returncode = os.waitstatus_to_exitcode(status)
        stdout = stdout_path.read_text(errors="replace")
        stderr = stderr_path.read_text(errors="replace")
    # Linux reports KiB and Darwin bytes for ru_maxrss.
    peak_rss_kib = int(usage.ru_maxrss // 1024 if sys.platform == "darwin" else usage.ru_maxrss)
    record = {
        "argv": command,
        "returncode": process.returncode,
        "stdout": stdout,
        "stderr": stderr,
        "user_cpu_ns": round(usage.ru_utime * 1_000_000_000),
        "system_cpu_ns": round(usage.ru_stime * 1_000_000_000),
        "peak_rss_kib": peak_rss_kib,
        "environment": recorded_environment,
    }
    with log.open("ab") as stream:
        stream.write(canonical_json(record))
        stream.flush()
        os.fsync(stream.fileno())
    return CommandResult(
        command, process.returncode, stdout, stderr,
        usage.ru_utime, usage.ru_stime,
        peak_rss_kib, recorded_environment,
    )


@dataclass(frozen=True)
class ObjectInfo:
    key: str
    size: int
    sha256: str | None
    etag: str
    last_modified: str
    metadata: dict[str, str]
    tags: dict[str, str]
    tagging_request_id: str | None = None
    version_id: str | None = None


class ObjectStore(Protocol):
    def head(self, key: str) -> ObjectInfo: ...
    def download(self, key: str, destination: Path) -> ObjectInfo: ...
    def put_immutable(self, key: str, source: Path, metadata: dict[str, str]) -> ObjectInfo: ...
    def put_bytes_immutable(self, key: str, value: bytes, metadata: dict[str, str]) -> ObjectInfo: ...
    def add_tag_preserving(self, key: str, name: str, value: str) -> ObjectInfo: ...


class LocalObjectStore:
    """Filesystem object store used for complete local transaction tests.

    Object bytes live below ``objects/`` and metadata below ``meta/``.  The
    immutable-put and tag semantics intentionally mirror the production gates.
    """

    def __init__(self, root: Path):
        self.root = root.resolve()
        self.objects = self.root / "objects"
        self.meta = self.root / "meta"
        self.objects.mkdir(parents=True, exist_ok=True)
        self.meta.mkdir(parents=True, exist_ok=True)

    def _validate_key(self, key: str) -> None:
        path = Path(key)
        if path.is_absolute() or not path.parts or any(part in ("", ".", "..") for part in path.parts):
            raise ReplayError(f"unsafe object key: {key!r}")

    def _paths(self, key: str) -> tuple[Path, Path]:
        self._validate_key(key)
        return self.objects / key, self.meta / f"{key}.json"

    def _read(self, key: str) -> tuple[Path, dict[str, Any]]:
        object_path, meta_path = self._paths(key)
        if not object_path.is_file() or not meta_path.is_file():
            raise ReplayError(f"missing object: {key}")
        meta = load_json(meta_path)
        return object_path, meta

    def head(self, key: str) -> ObjectInfo:
        path, meta = self._read(key)
        digest = sha256_file(path)
        if meta.get("sha256") != digest or meta.get("size") != path.stat().st_size:
            raise ReplayError(f"stored object integrity mismatch: {key}")
        visible_digest = (
            None if meta.get("metadata", {}).get("simulate-head-without-sha256") == "true"
            else digest
        )
        return ObjectInfo(
            key, path.stat().st_size, visible_digest, meta["etag"], meta["last_modified"],
            dict(meta.get("metadata", {})), dict(meta.get("tags", {})),
            meta.get("tagging_request_id"), meta.get("version_id"),
        )

    def download(self, key: str, destination: Path) -> ObjectInfo:
        info = self.head(key)
        source, _ = self._read(key)
        atomic_write(destination, source.read_bytes())
        downloaded_sha = sha256_file(destination)
        if info.sha256 is not None and downloaded_sha != info.sha256:
            raise ReplayError(f"download read-back mismatch: {key}")
        return ObjectInfo(
            info.key, info.size, downloaded_sha, info.etag, info.last_modified,
            info.metadata, info.tags, info.tagging_request_id, info.version_id,
        )

    def put_immutable(self, key: str, source: Path, metadata: dict[str, str]) -> ObjectInfo:
        return self.put_bytes_immutable(key, source.read_bytes(), metadata)

    def put_bytes_immutable(self, key: str, value: bytes, metadata: dict[str, str]) -> ObjectInfo:
        object_path, meta_path = self._paths(key)
        digest = sha256_bytes(value)
        if object_path.exists() or meta_path.exists():
            current = self.head(key)
            if current.sha256 != digest or current.metadata != metadata:
                raise ReplayError(f"immutable object collision: {key}")
            return current
        atomic_write(object_path, value)
        record = {
            "size": len(value), "sha256": digest, "etag": digest,
            "last_modified": "local-immutable-v1", "metadata": metadata, "tags": {},
        }
        atomic_write(meta_path, canonical_json(record))
        return self.head(key)

    def add_tag_preserving(self, key: str, name: str, value: str) -> ObjectInfo:
        before = self.head(key)
        _, meta_path = self._paths(key)
        meta = load_json(meta_path)
        tags = dict(meta.get("tags", {}))
        tags[name] = value
        meta["tags"] = tags
        meta["tagging_request_id"] = f"local-put-tagging-{uuid.uuid4()}"
        atomic_write(meta_path, canonical_json(meta))
        after = self.head(key)
        if (after.etag, after.size, after.sha256, after.last_modified, after.version_id) != (
            before.etag, before.size, before.sha256, before.last_modified, before.version_id
        ):
            raise ReplayError(f"tagging changed object identity: {key}")
        return after

class AwsCliObjectStore:
    """Least-privilege S3 adapter used only by an explicitly launched worker."""

    def __init__(self, bucket: str, aws: str = "aws"):
        if not bucket or any(character.isspace() for character in bucket):
            raise ReplayError("invalid S3 bucket")
        self.bucket = bucket
        self.aws = aws

    def _json(self, arguments: list[str]) -> dict[str, Any]:
        completed = subprocess.run(
            [self.aws, *arguments, "--output", "json"], text=True,
            capture_output=True, check=False,
        )
        if completed.returncode != 0:
            raise ReplayError(
                f"aws {' '.join(arguments[:2])} failed rc={completed.returncode}: "
                f"{completed.stderr.strip()}"
            )
        try:
            value = json.loads(completed.stdout or "{}")
        except json.JSONDecodeError as error:
            raise ReplayError("aws returned malformed JSON") from error
        if not isinstance(value, dict):
            raise ReplayError("aws JSON result is not an object")
        return value

    def _json_with_request_id(self, arguments: list[str]) -> tuple[dict[str, Any], str]:
        completed = subprocess.run(
            [self.aws, *arguments, "--output", "json", "--debug"], text=True,
            capture_output=True, check=False,
        )
        if completed.returncode != 0:
            raise ReplayError(f"aws {' '.join(arguments[:2])} failed: {completed.stderr.strip()}")
        try:
            value = json.loads(completed.stdout or "{}")
        except json.JSONDecodeError as error:
            raise ReplayError("aws returned malformed JSON") from error
        matches = re.findall(
            r"(?i)[\"']?x-amz-request-id[\"']?\s*[:=]\s*[\"']?([A-Za-z0-9+/=_-]+)",
            completed.stderr,
        )
        if not isinstance(value, dict) or not matches:
            raise ReplayError("aws response lacks JSON object or x-amz-request-id")
        return value, matches[-1]

    def _head_or_none(self, key: str) -> ObjectInfo | None:
        completed = subprocess.run([
            self.aws, "s3api", "head-object", "--bucket", self.bucket,
            "--key", key, "--output", "json",
        ], text=True, capture_output=True, check=False)
        if completed.returncode != 0:
            lowered = (completed.stderr + completed.stdout).lower()
            if "not found" in lowered or "404" in lowered or "nosuchkey" in lowered:
                return None
            raise ReplayError(f"S3 HEAD failed for {key}: {completed.stderr.strip()}")
        try:
            head = json.loads(completed.stdout)
        except json.JSONDecodeError as error:
            raise ReplayError(f"S3 HEAD returned malformed JSON for {key}") from error
        tags_result, tagging_request_id = self._json_with_request_id([
            "s3api", "get-object-tagging", "--bucket", self.bucket, "--key", key,
        ])
        tags = {
            item["Key"]: item["Value"] for item in tags_result.get("TagSet", [])
            if isinstance(item, dict) and isinstance(item.get("Key"), str)
            and isinstance(item.get("Value"), str)
        }
        metadata = {
            str(name): str(value) for name, value in dict(head.get("Metadata", {})).items()
        }
        digest = metadata.get("sha256")
        if digest is not None:
            require_sha(digest, f"S3 metadata sha256 for {key}")
        return ObjectInfo(
            key=key, size=int(head["ContentLength"]), sha256=digest,
            etag=str(head["ETag"]).strip('"'),
            last_modified=str(head["LastModified"]), metadata=metadata, tags=tags,
            tagging_request_id=tagging_request_id,
            version_id=str(head["VersionId"]) if head.get("VersionId") is not None else None,
        )

    def head(self, key: str) -> ObjectInfo:
        result = self._head_or_none(key)
        if result is None:
            raise ReplayError(f"missing object: {key}")
        return result

    def download(self, key: str, destination: Path) -> ObjectInfo:
        before = self.head(key)
        destination.parent.mkdir(parents=True, exist_ok=True)
        arguments = [
            self.aws, "s3api", "get-object", "--bucket", self.bucket,
            "--key", key,
        ]
        if before.version_id is not None:
            arguments.extend(["--version-id", before.version_id])
        arguments.extend([str(destination), "--output", "json"])
        completed = subprocess.run(arguments, text=True, capture_output=True, check=False)
        if completed.returncode != 0:
            raise ReplayError(f"S3 GET failed for {key}: {completed.stderr.strip()}")
        downloaded_sha = sha256_file(destination)
        if destination.stat().st_size != before.size or (
            before.sha256 is not None and downloaded_sha != before.sha256
        ):
            raise ReplayError(f"S3 GET read-back mismatch: {key}")
        after = self.head(key)
        if (after.etag, after.size, after.last_modified, after.version_id) != (
            before.etag, before.size, before.last_modified, before.version_id
        ):
            raise ReplayError(f"S3 object changed during download: {key}")
        return ObjectInfo(
            after.key, after.size, downloaded_sha, after.etag, after.last_modified,
            after.metadata, after.tags, after.tagging_request_id, after.version_id,
        )

    def put_immutable(self, key: str, source: Path, metadata: dict[str, str]) -> ObjectInfo:
        digest = sha256_file(source)
        complete_metadata = dict(metadata, sha256=digest)

        def validate_winner(candidate: ObjectInfo) -> ObjectInfo:
            with tempfile.TemporaryDirectory() as temporary:
                downloaded = self.download(
                    key, Path(temporary) / "immutable-winner-readback")
            if (
                downloaded.size != source.stat().st_size
                or downloaded.sha256 != digest
                or downloaded.metadata != complete_metadata
                or candidate.etag != downloaded.etag
                or candidate.last_modified != downloaded.last_modified
                or candidate.version_id != downloaded.version_id
            ):
                raise ReplayError(f"immutable S3 collision: {key}")
            return downloaded

        current = self._head_or_none(key)
        if current is not None:
            return validate_winner(current)
        metadata_argument = ",".join(f"{name}={value}" for name, value in sorted(complete_metadata.items()))
        completed = subprocess.run([
            self.aws, "s3api", "put-object", "--bucket", self.bucket,
            "--key", key, "--body", str(source), "--metadata", metadata_argument,
            "--if-none-match", "*", "--output", "json",
        ], text=True, capture_output=True, check=False)
        if completed.returncode != 0:
            winner = self._head_or_none(key)
            if winner is not None:
                return validate_winner(winner)
            raise ReplayError(f"immutable S3 PUT failed for {key}: {completed.stderr.strip()}")
        uploaded = self.head(key)
        if uploaded.sha256 != digest or uploaded.size != source.stat().st_size:
            raise ReplayError(f"S3 PUT HEAD read-back mismatch: {key}")
        with tempfile.TemporaryDirectory() as temporary:
            self.download(key, Path(temporary) / "readback")
        return uploaded

    def put_bytes_immutable(self, key: str, value: bytes, metadata: dict[str, str]) -> ObjectInfo:
        with tempfile.TemporaryDirectory() as temporary:
            source = Path(temporary) / "object"
            source.write_bytes(value)
            return self.put_immutable(key, source, metadata)

    def add_tag_preserving(self, key: str, name: str, value: str) -> ObjectInfo:
        before = self.head(key)
        tags = dict(before.tags)
        tags[name] = value
        tag_set = [{"Key": key_name, "Value": tag_value} for key_name, tag_value in sorted(tags.items())]
        arguments = [
            self.aws, "s3api", "put-object-tagging", "--bucket", self.bucket, "--key", key,
            "--tagging", json.dumps({"TagSet": tag_set}, separators=(",", ":")),
        ]
        if before.version_id is not None:
            arguments.extend(["--version-id", before.version_id])
        arguments.extend(["--output", "json", "--debug"])
        completed = subprocess.run(arguments, text=True, capture_output=True, check=False)
        if completed.returncode != 0:
            raise ReplayError(f"S3 tagging failed for {key}: {completed.stderr.strip()}")
        after = self.head(key)
        if after.tags != tags:
            raise ReplayError(f"S3 tag read-back mismatch: {key}")
        if (after.etag, after.size, after.sha256, after.last_modified, after.version_id) != (
            before.etag, before.size, before.sha256, before.last_modified, before.version_id
        ):
            raise ReplayError(f"S3 tagging changed object identity: {key}")
        matches = re.findall(
            r"(?i)[\"']?x-amz-request-id[\"']?\s*[:=]\s*[\"']?([A-Za-z0-9+/=_-]+)",
            completed.stderr,
        )
        if not matches:
            raise ReplayError("S3 tagging response lacks x-amz-request-id")
        request_id = matches[-1]
        return ObjectInfo(
            after.key, after.size, after.sha256, after.etag, after.last_modified,
            after.metadata, after.tags, request_id, after.version_id,
        )

def info_record(info: ObjectInfo) -> dict[str, Any]:
    record = {
        "key": info.key, "size": info.size, "sha256": info.sha256,
        "etag": info.etag, "last_modified": info.last_modified,
        "metadata": info.metadata, "tags": info.tags,
    }
    if info.tagging_request_id is not None:
        record["tagging_request_id"] = info.tagging_request_id
    if info.version_id is not None:
        record["version_id"] = info.version_id
    return record
