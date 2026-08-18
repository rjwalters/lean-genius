#!/usr/bin/env python3
"""Stream a compact textual LRAT into Lean's binary LRAT representation.

The optional packed output stores the binary bitstream as 7-bit bytes.  It is
therefore valid UTF-8 and can be embedded with Lean's ``include_str``; the pure
Lean decoder ``parsePackedOrderFortyNineLratProof`` reverses the packing before
calling the standard LRAT parser and checker.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import tempfile
from pathlib import Path
from typing import BinaryIO, Iterable


class Output:
    def __init__(self, path: Path | None) -> None:
        self.path = path
        self.tmp_path: Path | None = None
        self.file: BinaryIO | None = None
        self.sha256 = hashlib.sha256()
        self.size = 0
        if path is not None:
            path.parent.mkdir(parents=True, exist_ok=True)
            fd, name = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
            self.tmp_path = Path(name)
            self.file = os.fdopen(fd, "wb")

    def write(self, data: bytes) -> None:
        self.sha256.update(data)
        self.size += len(data)
        if self.file is not None:
            self.file.write(data)

    def commit(self) -> None:
        if self.file is None or self.tmp_path is None or self.path is None:
            return
        self.file.flush()
        os.fsync(self.file.fileno())
        self.file.close()
        self.file = None
        os.replace(self.tmp_path, self.path)
        self.tmp_path = None

    def abort(self) -> None:
        if self.file is not None:
            self.file.close()
            self.file = None
        if self.tmp_path is not None:
            self.tmp_path.unlink(missing_ok=True)
            self.tmp_path = None


class SevenBitPacker:
    def __init__(self, output: Output) -> None:
        self.output = output
        self.acc = 0
        self.bits = 0
        self.buffer = bytearray()

    def write(self, data: bytes) -> None:
        for byte in data:
            self.acc |= byte << self.bits
            self.bits += 8
            while self.bits >= 7:
                self.buffer.append(self.acc & 0x7F)
                self.acc >>= 7
                self.bits -= 7
            if len(self.buffer) >= 1 << 20:
                self.output.write(self.buffer)
                self.buffer.clear()

    def finish(self) -> None:
        if self.bits:
            self.buffer.append(self.acc & 0x7F)
        if self.buffer:
            self.output.write(self.buffer)
            self.buffer.clear()


def encode_integer(value: int) -> bytes:
    if value == 0:
        raise ValueError("zero is a delimiter, not a binary LRAT integer")
    mapped = 2 * abs(value) if value > 0 else 2 * abs(value) + 1
    encoded = bytearray()
    while mapped:
        chunk = mapped & 0x7F
        mapped >>= 7
        encoded.append(chunk | (0x80 if mapped else 0))
    return bytes(encoded)


def encoded_action(tokens: list[str], line_number: int) -> Iterable[bytes]:
    if not tokens or tokens[0].startswith("c"):
        return
    try:
        step_id = int(tokens[0])
    except ValueError as error:
        raise ValueError(f"line {line_number}: invalid step id") from error
    if step_id <= 0:
        raise ValueError(f"line {line_number}: step id must be positive")

    if len(tokens) >= 2 and tokens[1] == "d":
        if tokens[-1] != "0" or tokens.count("0") != 1:
            raise ValueError(f"line {line_number}: malformed deletion")
        yield b"d"
        for token in tokens[2:-1]:
            value = int(token)
            if value <= 0:
                raise ValueError(
                    f"line {line_number}: deletion ids must be positive"
                )
            yield encode_integer(value)
        yield b"\0"
        return

    if tokens[-1] != "0" or tokens.count("0") != 2:
        raise ValueError(f"line {line_number}: addition must contain two zeros")
    yield b"a"
    yield encode_integer(step_id)
    for token in tokens[1:]:
        value = int(token)
        yield b"\0" if value == 0 else encode_integer(value)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path, help="compact textual LRAT")
    parser.add_argument("--binary-output", type=Path)
    parser.add_argument("--packed-output", type=Path)
    args = parser.parse_args()
    if args.binary_output is None and args.packed_output is None:
        parser.error("at least one output is required")
    return args


def main() -> int:
    args = parse_args()
    binary = Output(args.binary_output)
    packed = Output(args.packed_output)
    packer = SevenBitPacker(packed)
    actions = 0
    try:
        with args.input.open("r", encoding="ascii") as source:
            for line_number, line in enumerate(source, 1):
                tokens = line.split()
                if not tokens or tokens[0] == "c":
                    continue
                for chunk in encoded_action(tokens, line_number):
                    binary.write(chunk)
                    packer.write(chunk)
                actions += 1
        packer.finish()
        binary.commit()
        packed.commit()
    except Exception:
        binary.abort()
        packed.abort()
        raise

    print(json.dumps({
        "actions": actions,
        "binary_bytes": binary.size,
        "binary_sha256": binary.sha256.hexdigest(),
        "packed_bytes": packed.size,
        "packed_sha256": packed.sha256.hexdigest(),
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
