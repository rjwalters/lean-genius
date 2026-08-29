#!/usr/bin/env python3
"""Shared, fail-closed primitives for the H1 Lean replay stage."""

from __future__ import annotations

import hashlib
import json
import os
import re
import subprocess
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Protocol


TAG_RE = re.compile(r"[0-9a-f]{16}")
SHA_RE = re.compile(r"[0-9a-f]{64}")
SCHEMA = "erdos85-h1-replay-manifest-v1"
READY_SCHEMA = "erdos85-h1-replay-ready-v1"
RECEIPT_SCHEMA = "erdos85-h1-replay-receipt-v1"


class ReplayError(RuntimeError):
    """A fail-closed replay validation or transaction failure."""


def canonical_json(value: Any) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


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
    try:
        value = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as error:
        raise ReplayError(f"cannot read JSON {path}: {error}") from error
    if not isinstance(value, dict):
        raise ReplayError(f"{path}: top-level JSON must be an object")
    return value


def load_manifest(path: Path) -> dict[str, Any]:
    value = load_json(path)
    required_strings = (
        "schema", "campaign_prefix", "repository_commit", "inventory_sha256",
        "coverage_sha256", "toolchain_identity", "overlay_sha256",
        "generator_sha256", "template_sha256", "worker_sha256",
        "validator_sha256", "zstd_identity",
    )
    missing = [key for key in required_strings if not isinstance(value.get(key), str)]
    if missing:
        raise ReplayError(f"manifest missing string fields: {missing}")
    if value["schema"] != SCHEMA:
        raise ReplayError(f"unsupported manifest schema: {value['schema']!r}")
    for key in (
        "inventory_sha256", "coverage_sha256", "overlay_sha256",
        "generator_sha256", "template_sha256", "worker_sha256",
        "validator_sha256",
    ):
        require_sha(value[key], f"manifest.{key}")
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
    allowed = value.get("allowed_axioms")
    if not isinstance(allowed, list) or not all(isinstance(x, str) for x in allowed):
        raise ReplayError("manifest.allowed_axioms must be a string list")
    patterns = value.get("allowed_axiom_patterns", [])
    if not isinstance(patterns, list) or not all(isinstance(x, str) for x in patterns):
        raise ReplayError("manifest.allowed_axiom_patterns must be a string list")
    for pattern in patterns:
        if pattern in (".*", ".+") or len(pattern) > 512:
            raise ReplayError("manifest contains an overbroad axiom pattern")
        try:
            re.compile(pattern)
        except re.error as error:
            raise ReplayError(f"invalid axiom pattern {pattern!r}: {error}") from error
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


@dataclass(frozen=True)
class CommandResult:
    argv: list[str]
    returncode: int
    stdout: str
    stderr: str


def run_command(command: list[str], cwd: Path, log: Path) -> CommandResult:
    completed = subprocess.run(command, cwd=cwd, text=True, capture_output=True, check=False)
    record = {
        "argv": command,
        "returncode": completed.returncode,
        "stdout": completed.stdout,
        "stderr": completed.stderr,
    }
    with log.open("ab") as stream:
        stream.write(canonical_json(record))
        stream.flush()
        os.fsync(stream.fileno())
    return CommandResult(command, completed.returncode, completed.stdout, completed.stderr)


@dataclass(frozen=True)
class ObjectInfo:
    key: str
    size: int
    sha256: str
    etag: str
    last_modified: str
    metadata: dict[str, str]
    tags: dict[str, str]


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
        return ObjectInfo(
            key, path.stat().st_size, digest, meta["etag"], meta["last_modified"],
            dict(meta.get("metadata", {})), dict(meta.get("tags", {})),
        )

    def download(self, key: str, destination: Path) -> ObjectInfo:
        info = self.head(key)
        source, _ = self._read(key)
        atomic_write(destination, source.read_bytes())
        if sha256_file(destination) != info.sha256:
            raise ReplayError(f"download read-back mismatch: {key}")
        return info

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
        atomic_write(meta_path, canonical_json(meta))
        after = self.head(key)
        if (after.etag, after.size, after.sha256, after.last_modified) != (
            before.etag, before.size, before.sha256, before.last_modified
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
        tags_result = self._json([
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
        require_sha(digest, f"S3 metadata sha256 for {key}")
        return ObjectInfo(
            key=key, size=int(head["ContentLength"]), sha256=digest,
            etag=str(head["ETag"]).strip('"'),
            last_modified=str(head["LastModified"]), metadata=metadata, tags=tags,
        )

    def head(self, key: str) -> ObjectInfo:
        result = self._head_or_none(key)
        if result is None:
            raise ReplayError(f"missing object: {key}")
        return result

    def download(self, key: str, destination: Path) -> ObjectInfo:
        before = self.head(key)
        destination.parent.mkdir(parents=True, exist_ok=True)
        completed = subprocess.run([
            self.aws, "s3api", "get-object", "--bucket", self.bucket,
            "--key", key, str(destination), "--output", "json",
        ], text=True, capture_output=True, check=False)
        if completed.returncode != 0:
            raise ReplayError(f"S3 GET failed for {key}: {completed.stderr.strip()}")
        if destination.stat().st_size != before.size or sha256_file(destination) != before.sha256:
            raise ReplayError(f"S3 GET read-back mismatch: {key}")
        after = self.head(key)
        if (after.etag, after.size, after.sha256, after.last_modified) != (
            before.etag, before.size, before.sha256, before.last_modified
        ):
            raise ReplayError(f"S3 object changed during download: {key}")
        return after

    def put_immutable(self, key: str, source: Path, metadata: dict[str, str]) -> ObjectInfo:
        digest = sha256_file(source)
        complete_metadata = dict(metadata, sha256=digest)
        current = self._head_or_none(key)
        if current is not None:
            if current.sha256 != digest or any(current.metadata.get(k) != v for k, v in complete_metadata.items()):
                raise ReplayError(f"immutable S3 collision: {key}")
            return current
        metadata_argument = ",".join(f"{name}={value}" for name, value in sorted(complete_metadata.items()))
        completed = subprocess.run([
            self.aws, "s3api", "put-object", "--bucket", self.bucket,
            "--key", key, "--body", str(source), "--metadata", metadata_argument,
            "--if-none-match", "*", "--output", "json",
        ], text=True, capture_output=True, check=False)
        if completed.returncode != 0:
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
        self._json([
            "s3api", "put-object-tagging", "--bucket", self.bucket, "--key", key,
            "--tagging", json.dumps({"TagSet": tag_set}, separators=(",", ":")),
        ])
        after = self.head(key)
        if after.tags != tags:
            raise ReplayError(f"S3 tag read-back mismatch: {key}")
        if (after.etag, after.size, after.sha256, after.last_modified) != (
            before.etag, before.size, before.sha256, before.last_modified
        ):
            raise ReplayError(f"S3 tagging changed object identity: {key}")
        return after


def info_record(info: ObjectInfo) -> dict[str, Any]:
    return {
        "key": info.key, "size": info.size, "sha256": info.sha256,
        "etag": info.etag, "last_modified": info.last_modified,
        "metadata": info.metadata, "tags": info.tags,
    }
