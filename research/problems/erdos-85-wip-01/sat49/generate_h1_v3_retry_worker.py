#!/usr/bin/env python3
"""Derive a collision-safe H1 v3 retry worker from the audited v2 worker."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import stat
from pathlib import Path


KNOWN_V2_SHA256 = "c762e8bccefc596e889c4be91ee2dba545d54c6748dd1841e1ff75c2249f34fb"
SHA256_RE = re.compile(r"[0-9a-f]{64}")
HEAD_NOT_FOUND_RE = (
    r"^(aws: \[ERROR\]: )?An error occurred "
    r"\((404|NotFound|NoSuchKey)\) when calling the HeadObject operation:"
)


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def stable_read(path: Path) -> bytes:
    before = path.stat()
    with path.open("rb") as stream:
        opened_before = os.fstat(stream.fileno())
        data = stream.read()
        opened_after = os.fstat(stream.fileno())
    after = path.stat()
    identity = lambda value: (
        value.st_dev, value.st_ino, value.st_size, value.st_mtime_ns
    )
    if not stat.S_ISREG(opened_before.st_mode) or not (
        identity(before) == identity(opened_before)
        == identity(opened_after) == identity(after)
    ):
        raise ValueError(f"{path}: input changed while being read")
    return data


def atomic_write(path: Path, data: bytes, mode: int) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.tmp.{os.getpid()}")
    try:
        temporary.write_bytes(data)
        temporary.chmod(mode)
        os.link(temporary, path)
    finally:
        temporary.unlink(missing_ok=True)


def replace_once(text: str, old: str, new: str, label: str) -> str:
    if text.count(old) != 1:
        raise ValueError(f"v2 worker drift: expected exactly one {label}")
    return text.replace(old, new, 1)


def derive_worker(source: bytes) -> bytes:
    if sha256_bytes(source) != KNOWN_V2_SHA256:
        raise ValueError("v2 worker SHA-256 does not match the audited source")
    text = source.decode("utf-8")
    if text.count("h1-fleet-v2/") != 3:
        raise ValueError("v2 worker drift: expected exactly three namespace layout comments")
    text = text.replace("h1-fleet-v2/", "h1-fleet-v3/")
    text = replace_once(
        text,
        "META=h1-fleet-v2",
        "META=h1-fleet-v3",
        "metadata namespace assignment",
    )
    picker = """  while IFS=$'\\t' read -r tag prof fam idx; do
    grep -qx \"$tag\" /opt/h1/ledger.$SLOT && continue
"""
    collision_safe_picker = """  while IFS=$'\\t' read -r tag prof fam idx; do
    # The retry queue is immutable, but a certificate can land after its
    # coverage snapshot.  Proceed only after an explicit NotFound response;
    # permission, network, throttle, and service errors quarantine the lane.
    if aws s3api head-object --bucket \"$B\" --key \"$PFX/h1/$tag.compact.lrat.gz\" > /dev/null 2> \"/opt/h1/head-object.$SLOT.err\"; then
      continue
    elif ! grep -Eq '__HEAD_NOT_FOUND_RE__' \"/opt/h1/head-object.$SLOT.err\"; then
      # Publish an immediate, explicit off-box marker.  A fail-closed HEAD
      # permission/transport error must never resemble an exhausted queue
      # while the supervisor is still waiting to upload its first heartbeat.
      HEAD_ERROR=$(head -c 512 \"/opt/h1/head-object.$SLOT.err\" | tr '\\n' ' ')
      HEAD_FAILURE=/opt/h1/head-precheck.$SLOT.failure.line
      HEAD_FAILURE_KEY=\"$PFX/$META/failures/$tag.head-precheck.$NODE.$SLOT.line\"
      printf '%s %s HEAD-PRECHECK-FAIL node=%s slot=%s error=%s\\n' \\
        \"$(date -u +%FT%TZ)\" \"$tag\" \"$NODE\" \"$SLOT\" \"$HEAD_ERROR\" > \"$HEAD_FAILURE\"
      aws s3api put-object --bucket \"$B\" --key \"$HEAD_FAILURE_KEY\" \\
        --body \"$HEAD_FAILURE\" --if-none-match '*' > /dev/null 2>&1 || true
      log \"CERT-PRECHECK-FAIL tag=$tag marker=$HEAD_FAILURE_KEY; indeterminate object state, stopping slot\"
      echo \"tag=$tag head-precheck-fail marker=$HEAD_FAILURE_KEY\" > /opt/h1/slot.$SLOT.failed
      exit 1
    fi
    grep -qx \"$tag\" /opt/h1/ledger.$SLOT && continue
""".replace("__HEAD_NOT_FOUND_RE__", HEAD_NOT_FOUND_RE)
    text = replace_once(text, picker, collision_safe_picker, "job picker insertion point")
    old_upload = (
        "aws s3 cp --only-show-errors $W/orbit.compact.lrat.gz "
        "s3://$B/$PFX/h1/$TAG.compact.lrat.gz > $W/upload.out 2>&1"
    )
    new_upload = (
        "aws s3api put-object --bucket \"$B\" "
        "--key \"$PFX/h1/$TAG.compact.lrat.gz\" "
        "--body \"$W/orbit.compact.lrat.gz\" --if-none-match '*' "
        "> $W/upload.out 2>&1"
    )
    text = replace_once(text, old_upload, new_upload, "certificate publication command")
    banner = (
        f"# GENERATED collision-safe v3 retry worker; audited-v2-sha256={KNOWN_V2_SHA256}\n"
    )
    return (text.splitlines(keepends=True)[0] + banner + "".join(text.splitlines(keepends=True)[1:])).encode()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--receipt-output", type=Path, required=True)
    args = parser.parse_args()
    if args.output == args.receipt_output:
        raise ValueError("output and receipt output must be distinct")
    for output_path in (args.output, args.receipt_output):
        if output_path.exists():
            raise FileExistsError(f"refusing to replace existing output: {output_path}")
    source = stable_read(args.source)
    output = derive_worker(source)
    atomic_write(args.output, output, 0o755)
    receipt = {
        "schema": "erdos85-h1-v3-retry-worker-receipt-v1",
        "source_sha256": sha256_bytes(source),
        "output_sha256": sha256_bytes(output),
        "generator_sha256": sha256_bytes(Path(__file__).read_bytes()),
        "metadata_namespace": "h1-fleet-v3",
        "existing_certificate_precheck": True,
        "certificate_publication": "put-object-if-none-match-star",
        "certificate_publication_race": "stop-quarantined-no-overwrite",
    }
    atomic_write(
        args.receipt_output,
        (json.dumps(receipt, indent=2, sort_keys=True) + "\n").encode(),
        0o644,
    )
    print(json.dumps(receipt, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
