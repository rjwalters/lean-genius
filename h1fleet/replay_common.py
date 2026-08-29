#!/usr/bin/env python3
"""Shared, fail-closed primitives for the H1 Lean replay stage."""

from __future__ import annotations

import hashlib
import json
import os
import re
import resource
import subprocess
import sys
import tempfile
import time
import uuid
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Protocol


TAG_RE = re.compile(r"[0-9a-f]{16}")
SHA_RE = re.compile(r"[0-9a-f]{64}")
SCHEMA = "erdos85-h1-replay-manifest-v1"
READY_SCHEMA = "erdos85-h1-replay-ready-v1"
RECEIPT_SCHEMA = "erdos85-h1-replay-receipt-v1"
NATIVE_AXIOM_PATTERN = (
    r"^Erdos85\.h1V2P[0-4]I[0-9]{5}Check\._native\.native_decide\.ax_[0-9]+$"
)


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
        "aws_cli_identity",
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
        if pattern != NATIVE_AXIOM_PATTERN:
            raise ReplayError("manifest axiom patterns must use the reviewed native leaf-root pattern")
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
    ttl = value.get("claim_ttl_seconds", 86400)
    if not isinstance(ttl, int) or ttl < 60:
        raise ReplayError("manifest.claim_ttl_seconds must be an integer >= 60")
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
    user_cpu_seconds: float
    system_cpu_seconds: float
    peak_rss_kib: int
    environment: dict[str, str]


def run_command(command: list[str], cwd: Path, log: Path,
                environment_allowlist: list[str] | None = None) -> CommandResult:
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    with tempfile.TemporaryDirectory() as temporary:
        metrics = Path(temporary) / "time.txt"
        time_arguments = (["/usr/bin/time", "-l", "-o", str(metrics)] if sys.platform == "darwin" else
                          ["/usr/bin/time", "-v", "-o", str(metrics)])
        completed = subprocess.run(
            [*time_arguments, *command], cwd=cwd, text=True,
            capture_output=True, check=False,
        )
        try:
            metrics_text = metrics.read_text()
        except OSError as error:
            raise ReplayError(f"cannot read per-command resource metrics: {error}") from error
    match = re.search(
        r"(?im)^\s*(?:Maximum resident set size \(kbytes\):\s*|([0-9]+)\s+maximum resident set size\s*$)",
        metrics_text,
    )
    if sys.platform == "darwin":
        if match is None or match.group(1) is None:
            raise ReplayError("cannot parse command peak RSS from BSD time")
        peak_rss_kib = int(match.group(1)) // 1024
    else:
        linux_match = re.search(r"(?im)^\s*Maximum resident set size \(kbytes\):\s*([0-9]+)\s*$", metrics_text)
        if linux_match is None:
            raise ReplayError("cannot parse command peak RSS from GNU time")
        peak_rss_kib = int(linux_match.group(1))
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    environment = {
        key: os.environ[key] for key in (environment_allowlist or []) if key in os.environ
    }
    record = {
        "argv": command,
        "returncode": completed.returncode,
        "stdout": completed.stdout,
        "stderr": completed.stderr,
        "user_cpu_seconds": after.ru_utime - before.ru_utime,
        "system_cpu_seconds": after.ru_stime - before.ru_stime,
        "peak_rss_kib": peak_rss_kib,
        "environment": environment,
    }
    with log.open("ab") as stream:
        stream.write(canonical_json(record))
        stream.flush()
        os.fsync(stream.fileno())
    return CommandResult(
        command, completed.returncode, completed.stdout, completed.stderr,
        after.ru_utime - before.ru_utime, after.ru_stime - before.ru_stime,
        peak_rss_kib, environment,
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


class ObjectStore(Protocol):
    def head(self, key: str) -> ObjectInfo: ...
    def download(self, key: str, destination: Path) -> ObjectInfo: ...
    def put_immutable(self, key: str, source: Path, metadata: dict[str, str]) -> ObjectInfo: ...
    def put_bytes_immutable(self, key: str, value: bytes, metadata: dict[str, str]) -> ObjectInfo: ...
    def add_tag_preserving(self, key: str, name: str, value: str) -> ObjectInfo: ...
    def acquire_claim(self, key: str, owner: str, now: float, ttl_seconds: int) -> str: ...
    def release_claim(self, key: str, owner: str, token: str, now: float) -> None: ...


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
            meta.get("tagging_request_id"),
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
            info.metadata, info.tags, info.tagging_request_id,
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
        if (after.etag, after.size, after.sha256, after.last_modified) != (
            before.etag, before.size, before.sha256, before.last_modified
        ):
            raise ReplayError(f"tagging changed object identity: {key}")
        return after

    def acquire_claim(self, key: str, owner: str, now: float, ttl_seconds: int) -> str:
        object_path, meta_path = self._paths(key)
        object_path.parent.mkdir(parents=True, exist_ok=True)
        meta_path.parent.mkdir(parents=True, exist_ok=True)
        token = str(uuid.uuid4())
        record = canonical_json({"owner": owner, "token": token, "expires_unix": now + ttl_seconds})
        try:
            descriptor = os.open(object_path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
        except FileExistsError:
            current = load_json(object_path)
            if current.get("expires_unix", now + 1) > now:
                raise ReplayError(f"live replay claim exists: {key}")
            # Local replacement is serialized by an adjacent O_EXCL lock.
            lock = object_path.with_suffix(object_path.suffix + ".lock")
            try:
                lock_fd = os.open(lock, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
            except FileExistsError as error:
                raise ReplayError(f"claim recovery is already in progress: {key}") from error
            try:
                os.close(lock_fd)
                current = load_json(object_path)
                if current.get("expires_unix", now + 1) > now:
                    raise ReplayError(f"live replay claim exists: {key}")
                atomic_write(object_path, record)
            finally:
                lock.unlink(missing_ok=True)
        else:
            with os.fdopen(descriptor, "wb") as stream:
                stream.write(record)
                stream.flush()
                os.fsync(stream.fileno())
        digest = sha256_bytes(record)
        atomic_write(meta_path, canonical_json({
            "size": len(record), "sha256": digest, "etag": digest,
            "last_modified": f"local-claim-{now}", "metadata": {}, "tags": {},
        }))
        return token

    def release_claim(self, key: str, owner: str, token: str, now: float) -> None:
        object_path, _ = self._paths(key)
        current = load_json(object_path)
        if current.get("owner") != owner or current.get("token") != token:
            raise ReplayError(f"replay claim ownership mismatch: {key}")
        current["expires_unix"] = now
        current["released"] = True
        value = canonical_json(current)
        atomic_write(object_path, value)
        _, meta_path = self._paths(key)
        digest = sha256_bytes(value)
        atomic_write(meta_path, canonical_json({
            "size": len(value), "sha256": digest, "etag": digest,
            "last_modified": f"local-claim-{now}", "metadata": {}, "tags": {},
        }))


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
        downloaded_sha = sha256_file(destination)
        if destination.stat().st_size != before.size or (
            before.sha256 is not None and downloaded_sha != before.sha256
        ):
            raise ReplayError(f"S3 GET read-back mismatch: {key}")
        after = self.head(key)
        if (after.etag, after.size, after.last_modified) != (
            before.etag, before.size, before.last_modified
        ):
            raise ReplayError(f"S3 object changed during download: {key}")
        return ObjectInfo(
            after.key, after.size, downloaded_sha, after.etag, after.last_modified,
            after.metadata, after.tags, after.tagging_request_id,
        )

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
        completed = subprocess.run([
            self.aws, "s3api", "put-object-tagging", "--bucket", self.bucket, "--key", key,
            "--tagging", json.dumps({"TagSet": tag_set}, separators=(",", ":")),
            "--output", "json", "--debug",
        ], text=True, capture_output=True, check=False)
        if completed.returncode != 0:
            raise ReplayError(f"S3 tagging failed for {key}: {completed.stderr.strip()}")
        after = self.head(key)
        if after.tags != tags:
            raise ReplayError(f"S3 tag read-back mismatch: {key}")
        if (after.etag, after.size, after.sha256, after.last_modified) != (
            before.etag, before.size, before.sha256, before.last_modified
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
            after.metadata, after.tags, request_id,
        )

    def acquire_claim(self, key: str, owner: str, now: float, ttl_seconds: int) -> str:
        token = str(uuid.uuid4())
        value = canonical_json({"owner": owner, "token": token, "expires_unix": now + ttl_seconds})
        with tempfile.TemporaryDirectory() as temporary:
            source = Path(temporary) / "claim.json"
            source.write_bytes(value)
            completed = subprocess.run([
                self.aws, "s3api", "put-object", "--bucket", self.bucket, "--key", key,
                "--body", str(source), "--metadata", f"sha256={sha256_bytes(value)}",
                "--if-none-match", "*", "--output", "json",
            ], text=True, capture_output=True, check=False)
        if completed.returncode == 0:
            return token
        current = self._head_or_none(key)
        if current is None:
            raise ReplayError(f"claim creation failed: {completed.stderr.strip()}")
        with tempfile.TemporaryDirectory() as temporary:
            target = Path(temporary) / "claim.json"
            self.download(key, target)
            claim = load_json(target)
            if claim.get("expires_unix", now + 1) > now:
                raise ReplayError(f"live replay claim exists: {key}")
            source = Path(temporary) / "replacement.json"
            source.write_bytes(value)
            replaced = subprocess.run([
                self.aws, "s3api", "put-object", "--bucket", self.bucket, "--key", key,
                "--body", str(source), "--metadata", f"sha256={sha256_bytes(value)}",
                "--if-match", current.etag, "--output", "json",
            ], text=True, capture_output=True, check=False)
        if replaced.returncode != 0:
            raise ReplayError(f"stale claim replacement failed: {replaced.stderr.strip()}")
        return token

    def release_claim(self, key: str, owner: str, token: str, now: float) -> None:
        current = self.head(key)
        with tempfile.TemporaryDirectory() as temporary:
            downloaded = Path(temporary) / "claim.json"
            self.download(key, downloaded)
            claim = load_json(downloaded)
            if claim.get("owner") != owner or claim.get("token") != token:
                raise ReplayError(f"replay claim ownership mismatch: {key}")
            claim["expires_unix"] = now
            claim["released"] = True
            value = canonical_json(claim)
            replacement = Path(temporary) / "released.json"
            replacement.write_bytes(value)
            completed = subprocess.run([
                self.aws, "s3api", "put-object", "--bucket", self.bucket, "--key", key,
                "--body", str(replacement), "--metadata", f"sha256={sha256_bytes(value)}",
                "--if-match", current.etag, "--output", "json",
            ], text=True, capture_output=True, check=False)
        if completed.returncode != 0:
            raise ReplayError(f"claim release failed: {completed.stderr.strip()}")


def info_record(info: ObjectInfo) -> dict[str, Any]:
    record = {
        "key": info.key, "size": info.size, "sha256": info.sha256,
        "etag": info.etag, "last_modified": info.last_modified,
        "metadata": info.metadata, "tags": info.tags,
    }
    if info.tagging_request_id is not None:
        record["tagging_request_id"] = info.tagging_request_id
    return record
