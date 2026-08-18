#!/usr/bin/env python3
"""Reproducibly LZ4-compress and 7-bit-pack a native binary LRAT file."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import subprocess
import tempfile
from pathlib import Path
from typing import BinaryIO


CHUNK = 1 << 20
LZ4_ARGS = (
    "-q", "-f", "-12", "-T1", "-BI", "-B7", "--content-size",
    "--no-frame-crc",
)


def file_digest(path: Path) -> tuple[int, str]:
    digest = hashlib.sha256()
    size = 0
    with path.open("rb") as source:
        while chunk := source.read(CHUNK):
            digest.update(chunk)
            size += len(chunk)
    return size, digest.hexdigest()


def atomic_target(path: Path) -> tuple[BinaryIO, Path]:
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, name = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    return os.fdopen(fd, "wb"), Path(name)


def pack_seven_bit(source_path: Path, output_path: Path) -> tuple[int, str]:
    output, temporary = atomic_target(output_path)
    digest = hashlib.sha256()
    size = 0
    acc = 0
    bits = 0
    packed = bytearray()
    try:
        with source_path.open("rb") as source, output:
            while chunk := source.read(CHUNK):
                for byte in chunk:
                    acc |= byte << bits
                    bits += 8
                    while bits >= 7:
                        packed.append(acc & 0x7F)
                        acc >>= 7
                        bits -= 7
                    if len(packed) >= CHUNK:
                        output.write(packed)
                        digest.update(packed)
                        size += len(packed)
                        packed.clear()
            if bits:
                packed.append(acc & 0x7F)
            if packed:
                output.write(packed)
                digest.update(packed)
                size += len(packed)
            output.flush()
            os.fsync(output.fileno())
        os.replace(temporary, output_path)
    except Exception:
        temporary.unlink(missing_ok=True)
        raise
    return size, digest.hexdigest()


def verify_lz4_roundtrip(
    lz4: Path, frame: Path, expected_size: int, expected_sha256: str
) -> None:
    process = subprocess.Popen(
        (str(lz4), "-q", "-d", "-c", str(frame)),
        stdout=subprocess.PIPE,
    )
    assert process.stdout is not None
    digest = hashlib.sha256()
    size = 0
    while chunk := process.stdout.read(CHUNK):
        digest.update(chunk)
        size += len(chunk)
    return_code = process.wait()
    if return_code != 0:
        raise RuntimeError(f"lz4 roundtrip exited {return_code}")
    if size != expected_size or digest.hexdigest() != expected_sha256:
        raise RuntimeError("lz4 roundtrip differs from binary LRAT input")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path, help="native binary LRAT")
    parser.add_argument("--frame-output", type=Path)
    parser.add_argument("--packed-output", type=Path)
    parser.add_argument("--lz4", type=Path, default=None)
    args = parser.parse_args()
    if args.frame_output is None and args.packed_output is None:
        parser.error("at least one output is required")
    outputs = [path.resolve() for path in (args.frame_output, args.packed_output)
               if path is not None]
    if len(outputs) != len(set(outputs)) or args.input.resolve() in outputs:
        parser.error("input and output paths must be distinct")
    return args


def main() -> int:
    args = parse_args()
    lz4_name = str(args.lz4) if args.lz4 is not None else shutil.which("lz4")
    if lz4_name is None:
        raise RuntimeError("lz4 executable not found")
    lz4 = Path(lz4_name).resolve()
    input_size, input_sha256 = file_digest(args.input)
    lz4_size, lz4_sha256 = file_digest(lz4)
    version = subprocess.run(
        (str(lz4), "--version"), check=True, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
    ).stdout.strip()

    for output_path in (args.frame_output, args.packed_output):
        if output_path is not None:
            output_path.parent.mkdir(parents=True, exist_ok=True)
    temporary_directory = args.frame_output.parent if args.frame_output else \
        args.packed_output.parent
    temporary_directory.mkdir(parents=True, exist_ok=True)
    fd, name = tempfile.mkstemp(prefix=".h1-v2-lrat.", suffix=".lz4",
                                dir=temporary_directory)
    os.close(fd)
    temporary_frame = Path(name)
    try:
        subprocess.run(
            (str(lz4), *LZ4_ARGS, str(args.input), str(temporary_frame)),
            check=True,
        )
        verify_lz4_roundtrip(lz4, temporary_frame, input_size, input_sha256)
        frame_size, frame_sha256 = file_digest(temporary_frame)
        if args.packed_output is not None:
            packed_size, packed_sha256 = pack_seven_bit(
                temporary_frame, args.packed_output
            )
        else:
            packed_size, packed_sha256 = 0, ""
        if args.frame_output is not None:
            os.replace(temporary_frame, args.frame_output)
            temporary_frame = None
    finally:
        if temporary_frame is not None:
            temporary_frame.unlink(missing_ok=True)

    print(json.dumps({
        "binary_bytes": input_size,
        "binary_sha256": input_sha256,
        "frame_bytes": frame_size,
        "frame_sha256": frame_sha256,
        "lz4_args": list(LZ4_ARGS),
        "lz4_bytes": lz4_size,
        "lz4_sha256": lz4_sha256,
        "lz4_version": version,
        "packed_bytes": packed_size,
        "packed_sha256": packed_sha256,
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
