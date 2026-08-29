#!/usr/bin/env python3
"""Derive a receipt-gated Tier-A worker for the approved four-parent split."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path


SOURCE_WORKER_SHA256 = "f3969c22b9e9551685412ddc4af0e626e4732a2e40322d2b0135ed23de9db6d8"
OLD_GENERATOR_SHA256 = "81587780762f325d2d7507327332d76671996907c9d4166cb67a0f4e76784219"
OLD_MANIFEST_PATH = 'C / "nested/canonical_canary_third_manifest.json"'
OLD_MANIFEST_SHA256 = "630fc3ad396f6c6346643cffd6422ffd3fe1fa7a0f7318658c1df0c7088e4f19"
SHA_RE = re.compile(r"[0-9a-f]{64}")


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def atomic_write(path: Path, data: bytes, mode: int) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.tmp.{os.getpid()}")
    try:
        temporary.write_bytes(data)
        temporary.chmod(mode)
        os.replace(temporary, path)
    finally:
        temporary.unlink(missing_ok=True)


def replace_once(text: str, old: str, new: str, label: str) -> str:
    if text.count(old) != 1:
        raise ValueError(f"source worker drift: expected exactly one {label}")
    return text.replace(old, new, 1)


def derive_worker(
    source: bytes,
    generator_path: Path,
    generator_sha: str,
    manifest_path: Path,
    manifest_sha: str,
) -> bytes:
    if hashlib.sha256(source).hexdigest() != SOURCE_WORKER_SHA256:
        raise ValueError("source worker SHA-256 does not match the audited worker")
    text = source.decode()
    text = replace_once(
        text,
        f'"generator_sha": "{OLD_GENERATOR_SHA256}"',
        f'"generator_sha": "{generator_sha}"',
        "old third-generator SHA pin",
    )
    text = replace_once(
        text,
        f'"manifest": {OLD_MANIFEST_PATH}',
        f'"manifest": Path({json.dumps(str(manifest_path))})',
        "old third-manifest path pin",
    )
    text = replace_once(
        text,
        f'"manifest_sha": "{OLD_MANIFEST_SHA256}"',
        f'"manifest_sha": "{manifest_sha}"',
        "old third-manifest SHA pin",
    )
    banner = (
        "# GENERATED four-parent Tier-A worker; "
        f"audited-source-sha256={SOURCE_WORKER_SHA256}\n"
    )
    lines = text.splitlines(keepends=True)
    output = (lines[0] + banner + "".join(lines[1:])).encode()
    if str(generator_path) not in text:
        # The source uses its already-pinned TOOLS-relative generator path.
        # The caller's exact generator is authenticated separately below.
        expected_name = 'TOOLS / "generate_small_high_third_cube_jobs.py"'
        if text.count(expected_name) != 1:
            raise ValueError("source worker drift: third-generator path changed")
    return output


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-worker", type=Path, required=True)
    parser.add_argument("--third-generator", type=Path, required=True)
    parser.add_argument("--third-manifest", type=Path, required=True)
    parser.add_argument("--queue-receipt", type=Path, required=True)
    parser.add_argument("--expected-queue-receipt-sha256", required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--receipt-output", type=Path, required=True)
    args = parser.parse_args()
    if not SHA_RE.fullmatch(args.expected_queue_receipt_sha256):
        raise ValueError("expected queue receipt SHA-256 must be canonical lowercase hex")
    if sha256(args.queue_receipt) != args.expected_queue_receipt_sha256:
        raise ValueError("queue receipt SHA-256 mismatch")
    validation = subprocess.run(
        [
            sys.executable,
            str(args.third_generator),
            "validate-queue",
            "--receipt",
            str(args.queue_receipt),
            "--expected-receipt-sha256",
            args.expected_queue_receipt_sha256,
        ],
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
    )
    if validation.returncode != 0 or not validation.stdout.startswith("VALID "):
        raise ValueError(f"approved queue validation failed: {validation.stdout.strip()}")
    receipt_data = json.loads(args.queue_receipt.read_text())
    if Path(receipt_data.get("manifest", "")) != args.third_manifest:
        raise ValueError("queue receipt does not bind the requested third manifest")
    generator_sha = sha256(args.third_generator)
    manifest_sha = sha256(args.third_manifest)
    if receipt_data.get("manifest_sha256") != manifest_sha:
        raise ValueError("queue receipt third-manifest SHA mismatch")
    source = args.source_worker.read_bytes()
    output = derive_worker(
        source, args.third_generator, generator_sha, args.third_manifest, manifest_sha
    )
    atomic_write(args.output, output, 0o755)
    worker_receipt = {
        "schema": "erdos85-tierA-four-parent-worker-receipt-v1",
        "source_worker_sha256": hashlib.sha256(source).hexdigest(),
        "third_generator_sha256": generator_sha,
        "third_manifest_sha256": manifest_sha,
        "queue_receipt_sha256": args.expected_queue_receipt_sha256,
        "output_worker_sha256": hashlib.sha256(output).hexdigest(),
        "generator_sha256": sha256(Path(__file__)),
    }
    atomic_write(
        args.receipt_output,
        (json.dumps(worker_receipt, indent=2, sort_keys=True) + "\n").encode(),
        0o644,
    )
    print(json.dumps(worker_receipt, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
