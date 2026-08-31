#!/usr/bin/env python3
"""Candidate LRAT compactor with a bounded dense derived-ID map.

This is deliberately a new, post-live candidate.  It does not replace the
worker-pinned ``compact_h1_v2_lrat.py``.  Output semantics match that tool,
while the old-id map uses four bytes per slot instead of a Python dictionary.
"""

from __future__ import annotations

import argparse
from array import array
import hashlib
import os
import re
from pathlib import Path


UINT32_MAX = (1 << 32) - 1
DEFAULT_MAX_DERIVED_SPAN = 250_000_000
EXTEND_CHUNK = 1_000_000


def compact_lrat(source: Path, num_original: int, destination: Path,
                 max_derived_span: int = DEFAULT_MAX_DERIVED_SPAN) -> tuple[int, str]:
    if num_original < 0:
        raise ValueError("num_original must be nonnegative")
    if max_derived_span <= 0:
        raise ValueError("max_derived_span must be positive")
    first_derived = num_original + 1
    next_id = first_derived
    last_add = num_original
    seen_add = False
    mapping = array("I")
    if mapping.itemsize != 4:
        raise RuntimeError("dense LRAT map requires four-byte unsigned integers")
    previous_original_id = num_original
    output_lines = 0
    source_hash = hashlib.sha256()
    temporary = destination.with_name(f".{destination.name}.tmp.{os.getpid()}")

    def mapped(identifier: int) -> int:
        if identifier < first_derived:
            return identifier
        offset = identifier - first_derived
        if offset < 0 or offset >= len(mapping) or mapping[offset] == 0:
            raise ValueError(f"forward or unknown derived identifier {identifier}")
        return mapping[offset]

    def record(original_id: int, compact_id: int) -> None:
        offset = original_id - first_derived
        span = offset + 1
        if span > max_derived_span:
            raise ValueError(
                f"derived identifier span {span} exceeds cap {max_derived_span}")
        if compact_id <= 0 or compact_id > UINT32_MAX:
            raise ValueError("compacted identifier exceeds uint32")
        while span > len(mapping):
            count = min(EXTEND_CHUNK, span - len(mapping))
            mapping.extend(array("I", [0]) * count)
        if mapping[offset] != 0:
            raise ValueError(f"duplicate derived identifier {original_id}")
        mapping[offset] = compact_id

    destination.parent.mkdir(parents=True, exist_ok=True)
    try:
        with source.open("rb") as src, temporary.open("w", encoding="ascii") as dst:
            for line_number, raw in enumerate(src, 1):
                source_hash.update(raw)
                if not raw.isascii():
                    raise ValueError(f"{source}:{line_number}: non-ASCII LRAT input")
                if not seen_add:
                    deletion = re.match(rb"\s*(\S+)\s+d(?:\s|$)", raw)
                    if deletion is not None:
                        if re.search(rb"(?:^|\s)0\s*$", raw) is None:
                            raise ValueError(f"{source}:{line_number}: unterminated deletion")
                        try:
                            action_id = int(deletion.group(1))
                        except ValueError as error:
                            raise ValueError(f"{source}:{line_number}: malformed deletion") from error
                        if action_id <= 0:
                            raise ValueError(f"{source}:{line_number}: nonpositive deletion identifier")
                        continue
                tokens = raw.decode("ascii").split()
                if not tokens:
                    continue
                if len(tokens) >= 2 and tokens[1] == "d":
                    if tokens[-1] != "0":
                        raise ValueError(f"{source}:{line_number}: unterminated deletion")
                    try:
                        action_id = int(tokens[0])
                        deleted = [int(token) for token in tokens[2:-1]]
                    except ValueError as error:
                        raise ValueError(f"{source}:{line_number}: malformed deletion") from error
                    if action_id <= 0 or any(identifier <= 0 for identifier in deleted):
                        raise ValueError(f"{source}:{line_number}: nonpositive deletion identifier")
                    if not seen_add:
                        continue
                    body = " ".join(str(mapped(identifier)) for identifier in deleted)
                    dst.write(f"{last_add} d {body} 0\n")
                    output_lines += 1
                    continue
                try:
                    original_id = int(tokens[0])
                    rest = [int(token) for token in tokens[1:]]
                    first_zero = rest.index(0)
                except (ValueError, IndexError) as error:
                    raise ValueError(f"{source}:{line_number}: malformed addition") from error
                if not rest or rest[-1] != 0:
                    raise ValueError(f"{source}:{line_number}: unterminated addition")
                literals = rest[:first_zero]
                hints = rest[first_zero + 1:-1]
                if original_id < first_derived:
                    raise ValueError(f"{source}:{line_number}: derived identifier {original_id} precedes {first_derived}")
                if original_id <= previous_original_id:
                    raise ValueError(f"{source}:{line_number}: non-increasing derived identifier {original_id}")
                if any(hint == 0 for hint in hints):
                    raise ValueError(f"{source}:{line_number}: zero proof hint")
                mapped_hints = [-mapped(-hint) if hint < 0 else mapped(hint) for hint in hints]
                record(original_id, next_id)
                previous_original_id = original_id
                body = literals + [0] + mapped_hints + [0]
                dst.write(f"{next_id} {' '.join(map(str, body))}\n")
                last_add = next_id
                next_id += 1
                seen_add = True
                output_lines += 1
            dst.flush()
            os.fsync(dst.fileno())
        os.replace(temporary, destination)
    except BaseException:
        if temporary.exists():
            temporary.unlink()
        raise
    return output_lines, source_hash.hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("num_original_clauses", type=int)
    parser.add_argument("destination", type=Path)
    parser.add_argument("--max-derived-span", type=int, default=DEFAULT_MAX_DERIVED_SPAN)
    args = parser.parse_args()
    if args.num_original_clauses < 0:
        parser.error("num_original_clauses must be nonnegative")
    if args.source.resolve() == args.destination.resolve():
        parser.error("source and destination must differ")
    lines, source_sha = compact_lrat(
        args.source, args.num_original_clauses, args.destination,
        args.max_derived_span)
    print(f"{args.destination}: {lines} lines, source_sha256={source_sha}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
