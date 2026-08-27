#!/usr/bin/env python3
"""Stream a drat-trim LRAT into the form consumed by Lean's LRAT checker.

The transformation is semantics-preserving and matches ``emit_lrat_compact.py``:

* derived clause identifiers are made consecutive, starting immediately after
  the original CNF clauses;
* every derived hint/deletion identifier is translated through that map; and
* deletion actions before the first addition are dropped.  Those deletions can
  contain nearly every original clause, dominate artifact size, and are
  checker-optional.

Unlike the original campaign helper, this implementation streams the input and
writes atomically.  It is suitable for multi-gigabyte certification artifacts.
"""

from __future__ import annotations

import argparse
import hashlib
import os
import re
from pathlib import Path


def compact_lrat(source: Path, num_original: int, destination: Path) -> tuple[int, str]:
    first_derived = num_original + 1
    next_id = first_derived
    last_add = num_original
    seen_add = False
    mapping: dict[int, int] = {}
    previous_original_id = num_original
    output_lines = 0
    source_hash = hashlib.sha256()
    temporary = destination.with_name(f".{destination.name}.tmp.{os.getpid()}")

    def mapped(identifier: int) -> int:
        if identifier < first_derived:
            return identifier
        try:
            return mapping[identifier]
        except KeyError as error:
            raise ValueError(f"forward or unknown derived identifier {identifier}") from error

    destination.parent.mkdir(parents=True, exist_ok=True)
    try:
        with source.open("rb") as src, temporary.open("w", encoding="ascii") as dst:
            for line_number, raw in enumerate(src, 1):
                source_hash.update(raw)
                if not raw.isascii():
                    raise ValueError(f"{source}:{line_number}: non-ASCII LRAT input")
                # drat-trim can emit a single multi-gigabyte deletion before its
                # first addition.  It is intentionally dropped, so avoid
                # splitting that line into millions of short Python strings.
                if not seen_add:
                    deletion = re.match(rb"\s*(\S+)\s+d(?:\s|$)", raw)
                    if deletion is not None:
                        if re.search(rb"(?:^|\s)0\s*$", raw) is None:
                            raise ValueError(
                                f"{source}:{line_number}: unterminated deletion"
                            )
                        try:
                            action_id = int(deletion.group(1))
                        except ValueError as error:
                            raise ValueError(
                                f"{source}:{line_number}: malformed deletion"
                            ) from error
                        if action_id <= 0:
                            raise ValueError(
                                f"{source}:{line_number}: nonpositive deletion identifier"
                            )
                        continue
                text = raw.decode("ascii")
                tokens = text.split()
                if not tokens:
                    continue

                if len(tokens) >= 2 and tokens[1] == "d":
                    if tokens[-1] != "0":
                        raise ValueError(f"{source}:{line_number}: unterminated deletion")
                    try:
                        action_id = int(tokens[0])
                    except ValueError as error:
                        raise ValueError(
                            f"{source}:{line_number}: malformed deletion"
                        ) from error
                    if action_id <= 0:
                        raise ValueError(
                            f"{source}:{line_number}: nonpositive deletion identifier"
                        )
                    if not seen_add:
                        continue
                    try:
                        deleted = [int(token) for token in tokens[2:-1]]
                    except ValueError as error:
                        raise ValueError(
                            f"{source}:{line_number}: malformed deletion"
                        ) from error
                    if any(identifier <= 0 for identifier in deleted):
                        raise ValueError(
                            f"{source}:{line_number}: nonpositive deletion identifier"
                        )
                    identifiers = [mapped(identifier) for identifier in deleted]
                    body = " ".join(map(str, identifiers))
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
                hints = rest[first_zero + 1 : -1]
                if original_id < first_derived:
                    raise ValueError(
                        f"{source}:{line_number}: derived identifier {original_id} "
                        f"precedes {first_derived}"
                    )
                if original_id <= previous_original_id:
                    raise ValueError(
                        f"{source}:{line_number}: non-increasing derived identifier "
                        f"{original_id}"
                    )
                if any(hint == 0 for hint in hints):
                    raise ValueError(f"{source}:{line_number}: zero proof hint")
                mapped_hints = [
                    -mapped(-hint) if hint < 0 else mapped(hint) for hint in hints
                ]
                if original_id in mapping:
                    raise ValueError(
                        f"{source}:{line_number}: duplicate derived identifier {original_id}"
                    )
                mapping[original_id] = next_id
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
    args = parser.parse_args()
    if args.num_original_clauses < 0:
        parser.error("num_original_clauses must be nonnegative")
    if args.source.resolve() == args.destination.resolve():
        parser.error("source and destination must differ")

    lines, source_sha = compact_lrat(
        args.source, args.num_original_clauses, args.destination
    )
    print(
        f"{args.destination}: {lines} lines, "
        f"{args.destination.stat().st_size / 1_048_576:.2f} MiB, "
        f"source_sha256={source_sha}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
