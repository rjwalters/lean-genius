#!/usr/bin/env python3
"""Generate and verify the two negative cover proofs for one CUBE25 orbit.

The certified ``v2cnf emit-cover`` command supplies the formulas.  PySAT's
Glucose 4.2 supplies DRAT proofs, and ``drat-trim`` independently verifies
each proof before a hash-addressable manifest is published.  The manifest is
written last, so a completed output directory is an atomic certification unit
for the later 27-member cube-bundle pipeline.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import tempfile
import time
from pathlib import Path

from pysat.formula import CNF
from pysat.solvers import Glucose42


SIDES = {
    "left": (-301, -302, -303, -304, -305),
    "right": (-456, -457, -458, -459, -460),
}


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def artifact(path: Path) -> dict[str, int | str]:
    return {"sha256": sha256(path), "bytes": path.stat().st_size}


def checked_executable(path: Path, label: str) -> Path:
    result = path.expanduser().resolve()
    if not result.is_file() or not os.access(result, os.X_OK):
        raise ValueError(f"{label} is not an executable file: {result}")
    return result


def validate_cover_cnf(path: Path, units: tuple[int, ...]) -> tuple[int, int]:
    header: tuple[int, int] | None = None
    clause_count = 0
    tail: list[tuple[int, ...]] = []
    with path.open() as stream:
        for line_number, raw in enumerate(stream, 1):
            line = raw.strip()
            if not line or line.startswith("c"):
                continue
            if line.startswith("p "):
                fields = line.split()
                if header is not None or len(fields) != 4 or fields[:2] != ["p", "cnf"]:
                    raise ValueError(f"{path}:{line_number}: malformed/duplicate header")
                header = (int(fields[2]), int(fields[3]))
                continue
            literals = tuple(map(int, line.split()))
            if not literals or literals[-1] != 0:
                raise ValueError(f"{path}:{line_number}: unterminated clause")
            clause_count += 1
            tail.append(literals)
            if len(tail) > len(units):
                tail.pop(0)
    if header is None:
        raise ValueError(f"{path}: missing DIMACS header")
    if clause_count != header[1]:
        raise ValueError(
            f"{path}: declared {header[1]} clauses but emitted {clause_count}"
        )
    expected_tail = [(unit, 0) for unit in units]
    if tail != expected_tail:
        raise ValueError(f"{path}: cover unit tail mismatch: {tail}")
    return header


def solve_cover(cnf_path: Path, drat_path: Path) -> dict[str, object]:
    formula = CNF(from_file=str(cnf_path))
    started = time.monotonic()
    with Glucose42(bootstrap_with=formula.clauses, with_proof=True) as solver:
        if solver.solve():
            raise RuntimeError(f"cover formula is SAT: {cnf_path}")
        proof = solver.get_proof()
        stats = solver.accum_stats()
    elapsed = time.monotonic() - started
    with drat_path.open("x") as stream:
        stream.write("\n".join(proof))
        stream.write("\n")
    return {
        "solver": "PySAT Glucose42",
        "seconds": round(elapsed, 6),
        "proof_lines": len(proof),
        "stats": stats,
    }


def verify_drat(drat_trim: Path, cnf_path: Path, drat_path: Path) -> dict[str, object]:
    started = time.monotonic()
    result = subprocess.run(
        [str(drat_trim), str(cnf_path), str(drat_path)],
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
    )
    elapsed = time.monotonic() - started
    if result.returncode != 0 or "s VERIFIED" not in result.stdout:
        excerpt = result.stdout[-4000:]
        raise RuntimeError(
            f"drat-trim rejected {drat_path} (exit {result.returncode}):\n{excerpt}"
        )
    return {"seconds": round(elapsed, 6), "verified": True}


def validate_existing(
    output_dir: Path,
    manifest_path: Path,
    orbit: str | None,
    profile: int,
    table: Path,
    v2cnf: Path,
    drat_trim: Path,
) -> None:
    manifest = json.loads(manifest_path.read_text())
    if manifest.get("schema") != "h1-v2-cube-covers-v1":
        raise ValueError(f"unsupported manifest schema in {manifest_path}")
    expected_provenance = {
        "orbit": orbit,
        "profile": profile,
        "table": artifact(table),
        "tools": {"v2cnf": artifact(v2cnf), "drat_trim": artifact(drat_trim)},
    }
    for key, expected in expected_provenance.items():
        if manifest.get(key) != expected:
            raise ValueError(f"manifest {key} does not match this invocation")
    for side, units in SIDES.items():
        entry = manifest["covers"][side]
        if entry.get("units") != list(units) or entry.get("drat_trim") is None:
            raise ValueError(f"manifest cover metadata mismatch: {side}")
        if entry["drat_trim"].get("verified") is not True:
            raise ValueError(f"manifest does not record VERIFIED DRAT: {side}")
        for kind in ("cnf", "drat"):
            path = output_dir / entry[kind]["file"]
            if not path.is_file():
                raise ValueError(f"manifest payload is missing: {path}")
            if artifact(path) != {
                "sha256": entry[kind]["sha256"],
                "bytes": entry[kind]["bytes"],
            }:
                raise ValueError(f"manifest payload mismatch: {path}")
        variables, clauses = validate_cover_cnf(
            output_dir / entry["cnf"]["file"], units
        )
        if (entry.get("variables"), entry.get("clauses")) != (variables, clauses):
            raise ValueError(f"manifest DIMACS metadata mismatch: {side}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--v2cnf", type=Path, required=True)
    parser.add_argument("--drat-trim", type=Path, required=True)
    parser.add_argument("--profile", type=int, choices=range(5), required=True)
    parser.add_argument("--table", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--orbit")
    args = parser.parse_args()

    v2cnf = checked_executable(args.v2cnf, "v2cnf")
    drat_trim = checked_executable(args.drat_trim, "drat-trim")
    table = args.table.expanduser().resolve()
    if not table.is_file():
        raise ValueError(f"table is not a file: {table}")
    if args.orbit is not None and not re.fullmatch(r"[0-9a-f]{16}", args.orbit):
        raise ValueError("--orbit must be a 16-digit lowercase hexadecimal tag")

    output_dir = args.output_dir.expanduser().resolve()
    output_dir.mkdir(parents=True, exist_ok=True)
    manifest_path = output_dir / "cover-manifest.json"
    if manifest_path.exists():
        validate_existing(
            output_dir, manifest_path, args.orbit, args.profile,
            table, v2cnf, drat_trim,
        )
        print(f"VALID {manifest_path}")
        return 0
    unexpected = [output_dir / f"{side}.cover.{kind}" for side in SIDES for kind in ("cnf", "drat")]
    if any(path.exists() for path in unexpected):
        raise ValueError(f"partial output exists without manifest in {output_dir}")

    temporary = Path(tempfile.mkdtemp(prefix=".cube-covers.", dir=output_dir))
    try:
        covers: dict[str, object] = {}
        for side, units in SIDES.items():
            cnf_path = temporary / f"{side}.cover.cnf"
            drat_path = temporary / f"{side}.cover.drat"
            with cnf_path.open("xb") as stream:
                emitted = subprocess.run(
                    [str(v2cnf), "emit-cover", str(args.profile), str(table), side],
                    check=False,
                    stdout=stream,
                )
            if emitted.returncode != 0:
                raise RuntimeError(f"v2cnf emit-cover {side} exited {emitted.returncode}")
            variables, clauses = validate_cover_cnf(cnf_path, units)
            solve = solve_cover(cnf_path, drat_path)
            verification = verify_drat(drat_trim, cnf_path, drat_path)
            covers[side] = {
                "units": list(units),
                "variables": variables,
                "clauses": clauses,
                "cnf": {"file": cnf_path.name, **artifact(cnf_path)},
                "drat": {"file": drat_path.name, **artifact(drat_path)},
                "solve": solve,
                "drat_trim": verification,
            }

        manifest = {
            "schema": "h1-v2-cube-covers-v1",
            "orbit": args.orbit,
            "profile": args.profile,
            "table": artifact(table),
            "tools": {"v2cnf": artifact(v2cnf), "drat_trim": artifact(drat_trim)},
            "covers": covers,
        }
        for side in SIDES:
            for kind in ("cnf", "drat"):
                source = temporary / covers[side][kind]["file"]
                os.replace(source, output_dir / source.name)
        temporary_manifest = temporary / manifest_path.name
        temporary_manifest.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
        os.replace(temporary_manifest, manifest_path)
    finally:
        shutil.rmtree(temporary, ignore_errors=True)

    print(f"VERIFIED {manifest_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
