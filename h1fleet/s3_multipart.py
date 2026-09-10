"""Conditional S3 multipart publication through AWS CLI, without live defaults.

This is the low-level publication step only. The caller must authenticate any
concurrent winner and perform full object readback before issuing its receipt.
No overwrite fallback or automatic retry occurs, including for HTTP 409/412.
Reference: https://docs.aws.amazon.com/AmazonS3/latest/userguide/conditional-writes.html
"""
from __future__ import annotations

import base64
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import subprocess
import tempfile

MIB = 1024 * 1024
MIN_PART = 5 * MIB
MAX_PART = 5 * 1024 * MIB
MAX_PARTS = 10000


class MultipartError(RuntimeError):
    """Publication failed or its acknowledgement could not be authenticated."""


def _pin(value: os.stat_result) -> tuple:
    return (value.st_dev, value.st_ino, value.st_size,
            value.st_mtime_ns, value.st_ctime_ns)


def conditional_multipart_upload(*, aws: str, bucket: str, key: str,
                                 source: Path, metadata: dict[str, str],
                                 expected_sha256: str, expected_size: int,
                                 part_size: int = 64 * MIB,
                                 runner=None) -> dict:
    """Publish once with checksum-bound parts and If-None-Match: *.

    Uses one part-sized temporary disk file and <=1 MiB Python read buffers.
    Source mutation, part errors, and malformed replies prevent completion.
    Failure after obtaining an upload ID triggers an abort attempt, scoped
    solely to that ID. Abort failure is surfaced with the original error.
    Success returns a publication acknowledgement, NOT a replay receipt.
    """
    runner = subprocess.run if runner is None else runner
    source = Path(source)
    if (type(expected_size) is not int or expected_size <= 0 or
            not isinstance(expected_sha256, str) or
            re.fullmatch(r"[0-9a-f]{64}", expected_sha256) is None):
        raise MultipartError("invalid source identity; empty files use single PUT")
    if (type(part_size) is not int or not MIN_PART <= part_size <= MAX_PART or
            (expected_size + part_size - 1) // part_size > MAX_PARTS):
        raise MultipartError("multipart size/count outside supported limits")
    if (not isinstance(metadata, dict) or
            any(not isinstance(k, str) or not isinstance(v, str)
                for k, v in metadata.items())):
        raise MultipartError("metadata must map strings to strings")
    if metadata.get("sha256", expected_sha256) != expected_sha256:
        raise MultipartError("metadata SHA256 differs from source identity")
    if not bucket or not key:
        raise MultipartError("bucket and key are required")
    complete_metadata = dict(metadata, sha256=expected_sha256)
    common = ["--bucket", bucket, "--key", key]

    def call(operation: str, arguments: list[str]) -> dict:
        result = runner([aws, "s3api", operation, *common, *arguments,
                         "--output", "json"],
                        text=True, capture_output=True, check=False)
        if result.returncode:
            raise MultipartError(f"{operation} failed: {result.stderr.strip()}")
        try:
            reply = json.loads(result.stdout or "{}")
        except (ValueError, TypeError) as exc:
            raise MultipartError(f"{operation}: invalid JSON") from exc
        if not isinstance(reply, dict) or "Error" in reply or "Code" in reply:
            raise MultipartError(f"{operation}: error or malformed response")
        return reply

    upload_id = None
    try:
        # Opening the source before initiating upload also avoids orphaning an
        # upload on ordinary missing/unreadable input failures.
        with source.open("rb") as stream:
            original = os.fstat(stream.fileno())
            if (not stat.S_ISREG(original.st_mode) or source.is_symlink() or
                    original.st_size != expected_size or
                    _pin(source.stat()) != _pin(original)):
                raise MultipartError("source is not the expected regular file")
            created = call("create-multipart-upload", [
                "--metadata", json.dumps(complete_metadata, sort_keys=True),
                "--checksum-algorithm", "SHA256"])
            upload_id = created.get("UploadId")
            if not isinstance(upload_id, str) or not upload_id:
                upload_id = None
                raise MultipartError("create response lacks upload ID")
            parts = []
            whole = hashlib.sha256()
            composite = hashlib.sha256()
            remaining = expected_size
            with tempfile.TemporaryDirectory(prefix="erdos85-multipart-") as raw:
                part_path = Path(raw) / "part"
                while remaining:
                    count = min(part_size, remaining)
                    part_hash = hashlib.sha256()
                    with part_path.open("wb") as target:
                        todo = count
                        while todo:
                            chunk = stream.read(min(MIB, todo))
                            if not chunk:
                                raise MultipartError("source truncated during upload")
                            target.write(chunk)
                            part_hash.update(chunk)
                            whole.update(chunk)
                            todo -= len(chunk)
                    checksum = base64.b64encode(part_hash.digest()).decode("ascii")
                    number = len(parts) + 1
                    uploaded = call("upload-part", [
                        "--upload-id", upload_id, "--part-number", str(number),
                        "--body", str(part_path), "--checksum-sha256", checksum])
                    if (not isinstance(uploaded.get("ETag"), str) or
                            not uploaded["ETag"] or
                            uploaded.get("ChecksumSHA256") != checksum):
                        raise MultipartError("part acknowledgement identity mismatch")
                    parts.append({"PartNumber": number, "ETag": uploaded["ETag"],
                                  "ChecksumSHA256": checksum})
                    composite.update(part_hash.digest())
                    remaining -= count
                if (stream.read(1) or whole.hexdigest() != expected_sha256 or
                        _pin(os.fstat(stream.fileno())) != _pin(original) or
                        source.is_symlink() or _pin(source.stat()) != _pin(original)):
                    raise MultipartError("source identity changed before completion")
                manifest = Path(raw) / "parts.json"
                manifest.write_text(json.dumps({"Parts": parts}, separators=(",", ":")))
                completed = call("complete-multipart-upload", [
                    "--upload-id", upload_id, "--multipart-upload", manifest.as_uri(),
                    "--if-none-match", "*"])
                expected_composite = (base64.b64encode(composite.digest()).decode("ascii")
                                      + f"-{len(parts)}")
                if (not isinstance(completed.get("ETag"), str) or not completed["ETag"] or
                        completed.get("ChecksumSHA256") != expected_composite):
                    raise MultipartError("completion acknowledgement identity mismatch")
                return {"upload_id": upload_id, "parts": len(parts),
                        "size": expected_size, "sha256": expected_sha256,
                        "checksum_sha256_composite": expected_composite,
                        "completion": completed}
    except BaseException as exc:
        if upload_id is not None:
            try:
                call("abort-multipart-upload", ["--upload-id", upload_id])
            except Exception as abort_error:
                raise MultipartError(
                    f"{exc}; abort failed for upload {upload_id}: {abort_error}") from exc
        raise
