#!/usr/bin/env python3
"""Materialize the checked 8-by-8 sub-cube cover for h7/t0 cube one."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import tempfile
from pathlib import Path


# One-based DIMACS identifiers.  The Lean cover module stores the corresponding
# zero-based Std.Sat variables.
LEFT = (1254, 1288, 1322, 1356, 1390, 1424, 1458, 1492)
RIGHT = (1254, 1519, 1546, 1573, 1600, 1627, 1654, 1681)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def inspect_dimacs(path: Path) -> tuple[int, int]:
    header = None
    clauses = 0
    with path.open("rb") as stream:
        for line_number, raw in enumerate(stream, 1):
            line = raw.strip()
            if not line or line.startswith(b"c"):
                continue
            if line.startswith(b"p"):
                fields = line.split()
                if (header is not None or len(fields) != 4 or
                        fields[:2] != [b"p", b"cnf"]):
                    raise ValueError(f"{path}:{line_number}: malformed header")
                header = (int(fields[2]), int(fields[3]))
                continue
            if not line.endswith(b" 0") and line != b"0":
                raise ValueError(f"{path}:{line_number}: unterminated clause")
            clauses += 1
    if header is None:
        raise ValueError(f"{path}: missing DIMACS header")
    if clauses != header[1]:
        raise ValueError(
            f"{path}: header declares {header[1]} clauses, found {clauses}"
        )
    return header


def jobs() -> list[dict[str, object]]:
    result: list[dict[str, object]] = [
        {"id": "h7_t0_cube1.cover-left", "kind": "cover-left",
         "units": [-literal for literal in LEFT]},
        {"id": "h7_t0_cube1.cover-right", "kind": "cover-right",
         "units": [-literal for literal in RIGHT]},
    ]
    for li, left in enumerate(LEFT):
        for ri, right in enumerate(RIGHT):
            result.append({
                "id": f"h7_t0_cube1.cube-{li}-{ri}",
                "kind": "cube", "left_index": li, "right_index": ri,
                "units": [left, right],
            })
    return result


def write_manifest(base: Path, output: Path) -> None:
    variables, clauses = inspect_dimacs(base)
    if max(LEFT + RIGHT) > variables:
        raise ValueError("selector exceeds the base CNF variable header")
    manifest = {
        "schema": "erdos85-h7-t0-cube1-cover-v1",
        "identifier_convention": "one-based DIMACS",
        "base": str(base.resolve()),
        "base_sha256": sha256(base),
        "variables": variables,
        "base_clauses": clauses,
        "left": list(LEFT),
        "right": list(RIGHT),
        "positive_cube_jobs": 64,
        "negative_cover_jobs": 2,
        "jobs": jobs(),
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    temporary = output.with_name(f".{output.name}.{os.getpid()}.tmp")
    temporary.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    os.replace(temporary, output)


def materialize(manifest_path: Path, job_id: str, output: Path) -> None:
    manifest = json.loads(manifest_path.read_text())
    if manifest.get("schema") != "erdos85-h7-t0-cube1-cover-v1":
        raise ValueError(f"unsupported manifest schema: {manifest_path}")
    matches = [job for job in manifest["jobs"] if job["id"] == job_id]
    if len(matches) != 1:
        raise ValueError(f"unknown or duplicated job id: {job_id}")
    base = Path(manifest["base"])
    if sha256(base) != manifest["base_sha256"]:
        raise ValueError(f"base CNF hash mismatch: {base}")
    units = matches[0]["units"]
    output.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary_name = tempfile.mkstemp(
        prefix=f".{output.name}.", suffix=".tmp", dir=output.parent
    )
    temporary = Path(temporary_name)
    try:
        with os.fdopen(fd, "wb") as target, base.open("rb") as source:
            replaced = False
            for raw in source:
                if raw.lstrip().startswith(b"p cnf"):
                    if replaced:
                        raise ValueError(f"duplicate DIMACS header: {base}")
                    target.write(
                        f"p cnf {manifest['variables']} "
                        f"{manifest['base_clauses'] + len(units)}\n".encode()
                    )
                    replaced = True
                else:
                    target.write(raw)
            if not replaced:
                raise ValueError(f"missing DIMACS header: {base}")
            for literal in units:
                target.write(f"{literal} 0\n".encode())
        inspect_dimacs(temporary)
        os.replace(temporary, output)
    finally:
        temporary.unlink(missing_ok=True)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    manifest_parser = subparsers.add_parser("manifest")
    manifest_parser.add_argument("--base", type=Path, required=True)
    manifest_parser.add_argument("--output", type=Path, required=True)
    materialize_parser = subparsers.add_parser("materialize")
    materialize_parser.add_argument("--manifest", type=Path, required=True)
    materialize_parser.add_argument("--job", required=True)
    materialize_parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.command == "manifest":
        write_manifest(args.base.resolve(), args.output.resolve())
    else:
        materialize(args.manifest.resolve(), args.job, args.output.resolve())
    print(f"WROTE {args.output.resolve()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
