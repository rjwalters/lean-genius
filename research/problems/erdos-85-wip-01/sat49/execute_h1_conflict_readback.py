#!/usr/bin/env python3
"""Read and validate the canonical objects in an H1 conflict audit queue."""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import os
import re
import shutil
import stat
import subprocess
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Protocol

import filter_h1_capacity_inventory as capacity
import generate_h1_conflict_readback_queue as queue_format


SCHEMA = "erdos85-h1-conflict-readback-audit-v1"
V2CNF_SHA256 = "4bd9604c6d670ad65a8ca332a26dbf35132418634a3b0678c177c8b2cfff4bf6"
LRATREPLAY_SHA256 = "37aad1d5c64a75fcb68e1ea587b2080b06c157a19c883b01d145b28b891c428c"
IMAGE = "lean4-arm64@sha256:a5ca6c4e3328a1832d5f9b814ab7c1e35616903b3956341962a5b1a96fb6dff6"
CACHE_VOLUME = "lean-mathlib-cache"
INVENTORY_SHA256 = "81d515472be48a43806f9c1c7343b4b715c98fe5a02a82e2b76244c1b015fd1b"
CAPACITY_FILTER_SHA256 = "a0f75f34d74cb8e3d48310b8f2e7b9544bba690110c0256c03f1b78bc9745e81"
QUEUE_FORMAT_SHA256 = "5acf5ba65a4d3ea3f1f2aa603b102aa762ebbf91b1b2365645cb0af9060e7636"
EXPECTED_COUNTS = (1485, 3617, 4717, 2693, 839)
EXPECTED_TOTAL = 13_351
SHA_RE = re.compile(r"[0-9a-f]{64}")
HEAD_MISSING_RE = re.compile(
    r"^An error occurred \((?:404|NotFound|NoSuchKey)\) when calling the HeadObject operation:"
)


class AuditError(RuntimeError):
    pass


class ObjectMissing(Exception):
    pass


@dataclass(frozen=True)
class Snapshot:
    data: bytes
    identity: tuple[int, int, int, int]
    sha256: str


@dataclass(frozen=True)
class Download:
    key: str
    size: int
    sha256: str
    etag: str
    last_modified: str
    version_id: str | None

    def record(self) -> dict:
        return {"etag": self.etag, "key": self.key,
                "last_modified": self.last_modified, "sha256": self.sha256,
                "size": self.size, "version_id": self.version_id}


class ReadOnlyStore(Protocol):
    def download(self, key: str, destination: Path) -> Download: ...


class Validator(Protocol):
    def validate(self, job: dict, inventory: dict, compact: Path,
                 work: Path) -> dict: ...


def canonical(value: object) -> bytes:
    return (json.dumps(value, ensure_ascii=True, allow_nan=False,
                       separators=(",", ":"), sort_keys=True) + "\n").encode("ascii")


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def snapshot(path: Path, expected_sha256: str, label: str) -> Snapshot:
    if not SHA_RE.fullmatch(expected_sha256):
        raise AuditError(f"{label}: invalid expected SHA-256")
    before = path.stat()
    with path.open("rb") as stream:
        opened_before = os.fstat(stream.fileno())
        data = stream.read()
        opened_after = os.fstat(stream.fileno())
    after = path.stat()
    identify = lambda item: (item.st_dev, item.st_ino, item.st_size, item.st_mtime_ns)
    if (path.is_symlink() or not stat.S_ISREG(opened_before.st_mode)
            or not identify(before) == identify(opened_before) == identify(opened_after) == identify(after)
            or sha256_bytes(data) != expected_sha256):
        raise AuditError(f"{label}: unstable or hash-mismatched input")
    return Snapshot(data, identify(after), expected_sha256)


def revalidate(path: Path, value: Snapshot, label: str) -> None:
    try:
        current = snapshot(path, value.sha256, label)
    except (AuditError, OSError) as error:
        raise AuditError(f"{label}: input changed before publication") from error
    if current.identity != value.identity or current.data != value.data:
        raise AuditError(f"{label}: input changed before publication")


def canonical_object(data: bytes, label: str) -> dict:
    try:
        value = json.loads(data)
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise AuditError(f"{label}: malformed JSON") from error
    if not isinstance(value, dict) or canonical(value) != data:
        raise AuditError(f"{label}: JSON is not canonical")
    return value


def parse_inputs(queue: Snapshot, queue_receipt: Snapshot, audit: Snapshot,
                 inventory: Snapshot) -> tuple[list[dict], dict[str, dict], dict]:
    receipt = canonical_object(queue_receipt.data, "queue receipt")
    expected_receipt_keys = {
        "audit_receipt_sha256", "certificate_prefix", "conflict_tags",
        "capacity_inventory_sha256", "coverage_sha256", "output_sha256",
        "profile_counts", "rows",
        "schema", "selection_status",
    }
    if (set(receipt) != expected_receipt_keys
            or receipt["schema"] != queue_format.QUEUE_SCHEMA
            or receipt["output_sha256"] != sha256_bytes(queue.data)
            or receipt["audit_receipt_sha256"] != sha256_bytes(audit.data)
            or receipt["capacity_inventory_sha256"] != sha256_bytes(inventory.data)
            or receipt["certificate_prefix"] != queue_format.CERTIFICATE_PREFIX
            or receipt["selection_status"] != "certificate-key-conflict"):
        raise AuditError("queue receipt crosslink mismatch")
    jobs = []
    seen = set()
    for number, raw in enumerate(queue.data.splitlines(keepends=True), 1):
        value = canonical_object(raw, f"queue row {number}")
        if set(value) != {"certificate_key", "family", "local_index", "profile", "tag"}:
            raise AuditError(f"queue row {number}: wrong schema")
        tag = value.get("tag")
        if tag in seen:
            raise AuditError("queue has duplicate tag")
        seen.add(tag)
        queue_format.validate_certificate_key(tag, value.get("certificate_key"))
        profile = value.get("profile")
        if (type(profile) is not int or profile not in range(5)
                or value.get("family") != queue_format.PROFILE_NAMES[profile]
                or type(value.get("local_index")) is not int or value["local_index"] < 0):
            raise AuditError(f"queue row {number}: invalid coordinates")
        jobs.append(value)
    if (not jobs or jobs != sorted(jobs, key=lambda item: item["tag"])
            or receipt["rows"] != len(jobs)
            or receipt["conflict_tags"] != [job["tag"] for job in jobs]):
        raise AuditError("queue census/order differs from receipt")
    counts = [sum(job["profile"] == profile for job in jobs) for profile in range(5)]
    if receipt["profile_counts"] != counts:
        raise AuditError("queue profile counts differ from receipt")

    rows: dict[str, dict] = {}
    locals_ = [0] * 5
    try:
        lines = inventory.data.decode("ascii").splitlines()
    except UnicodeDecodeError as error:
        raise AuditError("capacity inventory is not ASCII") from error
    for number, raw in enumerate(lines, 1):
        try:
            profile, *values = map(int, raw.split())
        except ValueError as error:
            raise AuditError(f"capacity row {number}: malformed") from error
        if (profile not in range(5) or len(values) != len(capacity.TABLE_PAIRS)
                or any(value not in range(5) for value in values)):
            raise AuditError(f"capacity row {number}: malformed")
        tag = capacity.worker_tag(tuple(values))
        if tag in rows:
            raise AuditError("capacity inventory has duplicate tag")
        rows[tag] = {"local_index": locals_[profile], "profile": profile,
                     "values": tuple(values)}
        locals_[profile] += 1
    if tuple(locals_) != EXPECTED_COUNTS or len(rows) != EXPECTED_TOTAL:
        raise AuditError("capacity inventory census mismatch")
    for job in jobs:
        row = rows.get(job["tag"])
        if row is None or (row["profile"], row["local_index"]) != (
                job["profile"], job["local_index"]):
            raise AuditError(f"{job['tag']}: queue/capacity coordinate mismatch")

    audit_value = canonical_object(audit.data, "coverage audit receipt")
    aws = audit_value.get("aws")
    if (audit_value.get("schema") != queue_format.AUDIT_SCHEMA
            or not isinstance(aws, dict) or set(aws) != {"bucket", "profile", "s3_prefix"}
            or any(not isinstance(value, str) or not value for value in aws.values())):
        raise AuditError("coverage audit AWS provenance mismatch")
    return jobs, rows, aws


def validate_compact_syntax(path: Path) -> None:
    final = None
    try:
        with path.open(encoding="ascii", errors="strict") as stream:
            for number, line in enumerate(stream, 1):
                tokens = line.split()
                if not tokens:
                    continue
                deletion = len(tokens) >= 2 and tokens[1] == "d"
                numeric_tokens = [tokens[0], *tokens[2:]] if deletion else tokens
                try:
                    [int(token) for token in numeric_tokens]
                except ValueError as error:
                    raise ValueError(f"line {number} is not integral") from error
                if deletion and len(tokens) < 3:
                    raise ValueError(f"deletion line {number} is malformed")
                if tokens[-1] != "0":
                    raise ValueError(f"line {number} lacks terminal zero")
                if not deletion:
                    final = tokens
    except UnicodeError as error:
        raise ValueError("compact LRAT is not ASCII") from error
    if final is None:
        raise ValueError("compact LRAT is empty")
    if len(final) < 3 or final[1] != "0":
        raise ValueError("compact LRAT lacks final empty-clause addition")


def execute(*, jobs: list[dict], inventory: dict[str, dict], store: ReadOnlyStore,
            validator: Validator, work: Path) -> list[dict]:
    results = []
    for job in jobs:
        tag = job["tag"]
        job_work = work / tag
        job_work.mkdir()
        compressed = job_work / "proof.lrat.gz"
        try:
            downloaded = store.download(job["certificate_key"], compressed)
        except ObjectMissing:
            results.append({"classification": "canonical-missing", "job": job,
                            "job_sha256": sha256_bytes(canonical(job)),
                            "reason": "confirmed-not-found"})
            continue
        if (downloaded.key != job["certificate_key"] or downloaded.size <= 0
                or downloaded.size != compressed.stat().st_size
                or downloaded.sha256 != sha256_file(compressed)):
            raise AuditError(f"{tag}: unstable or mismatched full readback")
        compact = job_work / "proof.lrat"
        compressed_record = downloaded.record()
        try:
            with gzip.open(compressed, "rb") as source, compact.open("xb") as target:
                shutil.copyfileobj(source, target)
            compact_sha = sha256_file(compact)
            compact_bytes = compact.stat().st_size
            if compact_bytes <= 0:
                raise ValueError("decompressed compact LRAT is empty")
            validate_compact_syntax(compact)
        except (OSError, EOFError, UnicodeError, ValueError) as error:
            results.append({"classification": "canonical-invalid",
                            "failure_stage": "gzip-or-compact-syntax", "job": job,
                            "job_sha256": sha256_bytes(canonical(job)),
                            "object": compressed_record, "reason": str(error)})
            continue
        validation = validator.validate(job, inventory[tag], compact, job_work)
        if set(validation) != {
                "cnf_bytes", "cnf_clauses", "cnf_sha256", "replay_accepted",
                "replay_rc", "replay_stderr_sha256", "replay_stdout_sha256",
                "table_sha256", "v2cnf_check"}:
            raise AuditError(f"{tag}: validator returned malformed evidence")
        if (type(validation["cnf_bytes"]) is not int or validation["cnf_bytes"] <= 0
                or type(validation["cnf_clauses"]) is not int or validation["cnf_clauses"] <= 0
                or any(not isinstance(validation[name], str) or not SHA_RE.fullmatch(validation[name])
                       for name in ("cnf_sha256", "replay_stderr_sha256",
                                    "replay_stdout_sha256", "table_sha256"))
                or not isinstance(validation["v2cnf_check"], str)
                or not re.fullmatch(r"MATCH \([0-9]+ clauses, top [0-9]+\)",
                                    validation["v2cnf_check"])):
            raise AuditError(f"{tag}: validator evidence fields are malformed")
        marker = re.fullmatch(r"MATCH \(([0-9]+) clauses, top ([0-9]+)\)",
                              validation["v2cnf_check"])
        assert marker is not None
        if int(marker.group(1)) != validation["cnf_clauses"]:
            raise AuditError(f"{tag}: validator clause count differs from check marker")
        base = {"compact_bytes": compact_bytes, "compact_lrat_sha256": compact_sha,
                "job": job, "job_sha256": sha256_bytes(canonical(job)),
                "object": compressed_record, "validation": validation}
        if validation["replay_rc"] == 1 and validation["replay_accepted"] is False:
            results.append({"classification": "canonical-invalid",
                            "failure_stage": "semantic-replay", "reason": "LRAT rejected",
                            **base})
            continue
        if validation["replay_rc"] != 0:
            raise AuditError(
                f"{tag}: replay runtime failed indeterminately "
                f"rc={validation['replay_rc']} "
                f"stdout_sha256={validation['replay_stdout_sha256']} "
                f"stderr_sha256={validation['replay_stderr_sha256']}")
        if validation["replay_accepted"] is True:
            results.append({"classification": "canonical-valid", **base})
        elif validation["replay_accepted"] is False:
            results.append({"classification": "canonical-invalid",
                            "failure_stage": "semantic-replay", "reason": "LRAT rejected",
                            **base})
        else:
            raise AuditError(f"{tag}: replay acceptance is not boolean")
    return results


class AwsCliReadOnlyStore:
    def __init__(self, aws: Path, profile: str, bucket: str):
        self.aws, self.profile, self.bucket = aws, profile, bucket

    def _run(self, arguments: list[str]) -> subprocess.CompletedProcess:
        environment = os.environ.copy()
        environment.update({"AWS_PROFILE": self.profile, "AWS_PAGER": "",
                            "AWS_EC2_METADATA_DISABLED": "true"})
        return subprocess.run([str(self.aws), *arguments], stdout=subprocess.PIPE,
                              stderr=subprocess.PIPE, text=True, env=environment)

    def _head(self, key: str, version: str | None = None) -> dict:
        arguments = ["s3api", "head-object", "--bucket", self.bucket, "--key", key,
                     "--output", "json"]
        if version is not None:
            arguments += ["--version-id", version]
        result = self._run(arguments)
        if result.returncode:
            if HEAD_MISSING_RE.match(result.stderr):
                raise ObjectMissing(key)
            raise AuditError(f"indeterminate HeadObject failure for {key}")
        try:
            value = json.loads(result.stdout)
        except json.JSONDecodeError as error:
            raise AuditError("HeadObject returned malformed JSON") from error
        required = ("ContentLength", "ETag", "LastModified")
        if not isinstance(value, dict) or any(name not in value for name in required):
            raise AuditError("HeadObject response is incomplete")
        return value

    @staticmethod
    def _identity(value: dict) -> tuple:
        return tuple(value.get(name) for name in (
            "ContentLength", "ETag", "LastModified", "VersionId"))

    def download(self, key: str, destination: Path) -> Download:
        first = self._head(key)
        version = first.get("VersionId")
        arguments = ["s3api", "get-object", "--bucket", self.bucket, "--key", key]
        if version is not None:
            arguments += ["--version-id", version]
        arguments += [str(destination)]
        result = self._run(arguments)
        if result.returncode:
            raise AuditError(f"indeterminate GetObject failure for {key}")
        try:
            second = self._head(key, version)
        except ObjectMissing as error:
            raise AuditError(f"object disappeared during readback: {key}") from error
        if self._identity(first) != self._identity(second):
            raise AuditError(f"object changed during readback: {key}")
        size = destination.stat().st_size
        if size != first["ContentLength"]:
            raise AuditError(f"truncated GetObject response for {key}")
        return Download(key, size, sha256_file(destination), first["ETag"],
                        first["LastModified"], version)


class LocalValidator:
    def __init__(self, docker: Path, image: str, cache_volume: str):
        self.docker, self.image, self.cache_volume = docker, image, cache_volume

    def cache_mount(self) -> list[str]:
        return ["-v", f"{self.cache_volume}:/cache:ro"]

    def validate(self, job: dict, inventory: dict, compact: Path, work: Path) -> dict:
        table_object = [[[left, right], value] for (left, right), value in
                        zip(capacity.TABLE_PAIRS, inventory["values"], strict=True) if value]
        table_data = (json.dumps(table_object) + "\n").encode("ascii")
        if hashlib.sha1(table_data[:-1]).hexdigest()[:16] != job["tag"]:
            raise AuditError(f"{job['tag']}: canonical table/tag mismatch")
        table = work / "table.json"; table.write_bytes(table_data)
        cnf = work / "orbit.cnf"
        base = [str(self.docker), "run", "--rm", "--network=none",
                *self.cache_mount(), "-v",
                f"{work}:/data:ro", "--entrypoint", "/cache/bin/v2cnf", self.image]
        with cnf.open("wb") as output:
            emit = subprocess.run([*base, "emit", str(job["profile"]), "/data/table.json"],
                                  stdout=output, stderr=subprocess.PIPE)
        if emit.returncode or not cnf.is_file() or cnf.stat().st_size == 0:
            raise AuditError(f"{job['tag']}: v2cnf emit failed")
        try:
            with cnf.open(encoding="ascii") as stream:
                header = next((line.split() for line in stream if line.startswith("p cnf ")), None)
        except UnicodeError as error:
            raise AuditError(f"{job['tag']}: emitted CNF is not ASCII") from error
        if (header is None or len(header) != 4 or not header[2].isdigit()
                or not header[3].isdigit() or int(header[3]) <= 0):
            raise AuditError(f"{job['tag']}: emitted CNF header is malformed")
        check = subprocess.run([*base, "check", str(job["profile"]), "/data/table.json",
                                "/data/orbit.cnf"], stdout=subprocess.PIPE,
                               stderr=subprocess.PIPE, text=True)
        marker = check.stdout.strip()
        match = re.fullmatch(r"MATCH \(([0-9]+) clauses, top ([0-9]+)\)", marker)
        if check.returncode or match is None:
            raise AuditError(f"{job['tag']}: v2cnf check failed")
        if int(match.group(1)) != int(header[3]):
            raise AuditError(f"{job['tag']}: CNF header/check clause mismatch")
        command = [str(self.docker), "run", "--rm", "--network=none",
                   *self.cache_mount(), "-v",
                   f"{work}:/data:ro", "--entrypoint", "/cache/bin/lratreplay",
                   self.image, "/data/orbit.cnf", "/data/proof.lrat"]
        replay = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        lines = replay.stdout.splitlines()
        accepted = (True if lines[-1:] == ["LRAT accepted: true"] else
                    False if lines[-1:] == ["LRAT accepted: false"] else None)
        return {"cnf_bytes": cnf.stat().st_size, "cnf_clauses": int(match.group(1)),
                "cnf_sha256": sha256_file(cnf), "replay_accepted": accepted,
                "replay_rc": replay.returncode,
                "replay_stderr_sha256": sha256_bytes(replay.stderr.encode()),
                "replay_stdout_sha256": sha256_bytes(replay.stdout.encode()),
                "table_sha256": sha256_bytes(table_data), "v2cnf_check": marker}

    def preflight(self) -> None:
        for path, expected in (("/cache/bin/v2cnf", V2CNF_SHA256),
                               ("/cache/bin/lratreplay", LRATREPLAY_SHA256)):
            result = subprocess.run(
                [str(self.docker), "run", "--rm", "--network=none",
                 *self.cache_mount(), "--entrypoint",
                 "/usr/bin/sha256sum", self.image, path],
                stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
            if result.returncode or result.stdout.split() != [expected, path]:
                raise AuditError(f"in-container {Path(path).name} pin mismatch")


def create_only(path: Path, data: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, raw = tempfile.mkstemp(prefix=f".{path.name}.tmp.", dir=path.parent)
    temporary = Path(raw)
    try:
        if temporary.is_symlink() or not stat.S_ISREG(os.fstat(descriptor).st_mode):
            raise AuditError("exclusive output temporary is not a regular file")
        os.fchmod(descriptor, 0o644)
        view = memoryview(data)
        while view:
            written = os.write(descriptor, view)
            if written <= 0:
                raise AuditError("short write to output temporary")
            view = view[written:]
        os.fsync(descriptor)
        os.close(descriptor)
        descriptor = -1
        os.link(temporary, path)
    finally:
        if descriptor >= 0:
            os.close(descriptor)
        temporary.unlink(missing_ok=True)


def command_version(path: Path, expected: str) -> None:
    result = subprocess.run([str(path), "--version"], stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, text=True)
    if result.returncode or result.stdout.strip() != expected:
        raise AuditError(f"{path}: version mismatch")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("queue", "queue-receipt", "audit-receipt", "capacity-inventory"):
        parser.add_argument(f"--{name}", type=Path, required=True)
        parser.add_argument(f"--{name}-sha256", required=True)
    for name in ("docker", "aws"):
        parser.add_argument(f"--{name}", type=Path, required=True)
        parser.add_argument(f"--{name}-sha256", required=True)
    parser.add_argument("--docker-version", required=True)
    parser.add_argument("--aws-version", required=True)
    parser.add_argument("--aws-profile", required=True)
    parser.add_argument("--bucket", required=True)
    parser.add_argument("--s3-prefix", required=True)
    parser.add_argument("--image", default=IMAGE)
    parser.add_argument("--cache-volume", required=True)
    parser.add_argument("--lratreplay-sha256", default=LRATREPLAY_SHA256)
    parser.add_argument("--executor-sha256", required=True)
    parser.add_argument("--capacity-filter-sha256", required=True)
    parser.add_argument("--queue-format-sha256", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(f"refusing to replace existing output: {args.output}")
    if (not args.output.is_absolute() or args.output.parent.is_symlink()
            or not args.output.parent.is_dir()):
        raise AuditError("output must be absent below an existing absolute non-symlink directory")
    paths = {name.replace("_", "-"): getattr(args, name) for name in (
        "queue", "queue_receipt", "audit_receipt", "capacity_inventory",
        "docker", "aws")}
    pins = {name: getattr(args, name.replace("-", "_") + "_sha256") for name in paths}
    snapshots = {name: snapshot(path, pins[name], name) for name, path in paths.items()}
    executor_path = Path(__file__).resolve()
    executor_snapshot = snapshot(executor_path, args.executor_sha256, "executor")
    helper_paths = {"capacity-filter": Path(capacity.__file__).resolve(),
                    "queue-format": Path(queue_format.__file__).resolve()}
    helper_pins = {"capacity-filter": args.capacity_filter_sha256,
                   "queue-format": args.queue_format_sha256}
    helper_snapshots = {name: snapshot(path, helper_pins[name], name)
                        for name, path in helper_paths.items()}
    if (pins["capacity-inventory"] != INVENTORY_SHA256
            or args.image != IMAGE or args.cache_volume != CACHE_VOLUME
            or args.lratreplay_sha256 != LRATREPLAY_SHA256):
        raise AuditError("trusted H1 tool/input pin mismatch")
    if helper_pins != {"capacity-filter": CAPACITY_FILTER_SHA256,
                       "queue-format": QUEUE_FORMAT_SHA256}:
        raise AuditError("trusted H1 helper pin mismatch")
    command_version(args.docker, args.docker_version)
    command_version(args.aws, args.aws_version)
    jobs, inventory, aws = parse_inputs(
        snapshots["queue"], snapshots["queue-receipt"], snapshots["audit-receipt"],
        snapshots["capacity-inventory"])
    if aws != {"bucket": args.bucket, "profile": args.aws_profile,
               "s3_prefix": args.s3_prefix} or args.s3_prefix != "sat49/campaign-20260825":
        raise AuditError("explicit AWS coordinates differ from pinned audit")
    store = AwsCliReadOnlyStore(args.aws, aws["profile"], aws["bucket"])
    validator = LocalValidator(args.docker, args.image, args.cache_volume)
    validator.preflight()
    with tempfile.TemporaryDirectory(prefix=".h1-conflict-readback-", dir=args.output.parent) as raw:
        results = execute(jobs=jobs, inventory=inventory, store=store,
                          validator=validator, work=Path(raw))
    for name, path in paths.items():
        revalidate(path, snapshots[name], name)
    revalidate(executor_path, executor_snapshot, "executor")
    for name, path in helper_paths.items():
        revalidate(path, helper_snapshots[name], name)
    receipt = {"aws": aws, "executor_sha256": args.executor_sha256,
               "helper_sha256": helper_pins,
               "image": args.image, "cache_volume": args.cache_volume,
               "input_paths": {name: str(path) for name, path in paths.items()},
               "inputs": pins,
               "lratreplay_sha256": args.lratreplay_sha256, "results": results,
               "schema": SCHEMA,
               "summary": {name: sum(row["classification"] == name for row in results)
                           for name in ("canonical-valid", "canonical-invalid", "canonical-missing")},
               "tool_versions": {"aws": args.aws_version, "docker": args.docker_version},
               "v2cnf_sha256": V2CNF_SHA256}
    create_only(args.output, canonical(receipt))
    print(f"WROTE {args.output} sha256={sha256_file(args.output)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
