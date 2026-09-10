#!/usr/bin/env python3
"""Strict input checks for bounded verdict-only CNF materialization.

The Lean v2 emitter's clause comparator ignores headers and empty clauses.
Pair its MATCH(count,top) with this validator; MATCH alone is insufficient.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re

MAX_INPUT_BYTES = 99_000_000
MAX_LINE_BYTES = 1_000_000
CLAUSE_LINE = re.compile(rb" *(-?[1-9][0-9]* +)*0 *")
MATCH = re.compile(r"MATCH \(([0-9]+) clauses, top ([0-9]+)\)")


def validate_dimacs(path: Path, *, expected_variables: int | None = None,
                    expected_clauses: int | None = None) -> dict:
    """Require emitter framing, including empty clauses; match the legacy parser.

General multi-line DIMACS is deliberately rejected: its clause boundaries can
disagree with the line-based native comparator even when total counts agree.
"""
    header = None
    count = 0
    size = 0
    digest = hashlib.sha256()
    with path.open("rb") as source:
        while line := source.readline(MAX_LINE_BYTES + 1):
            size += len(line)
            if size > MAX_INPUT_BYTES or len(line) > MAX_LINE_BYTES:
                raise ValueError("CNF exceeds bounded input/line size")
            digest.update(line)
            stripped = line.strip()
            if not stripped or stripped.startswith(b"c"):
                continue
            tokens = stripped.split()
            if tokens[0] == b"p":
                if header is not None or len(tokens) != 4 or tokens[1] != b"cnf":
                    raise ValueError("Missing, duplicate or invalid DIMACS header")
                if not all(re.fullmatch(rb"[0-9]+", x) for x in tokens[2:]):
                    raise ValueError("Invalid DIMACS header counts")
                header = tuple(map(int, tokens[2:]))
                continue
            if header is None:
                raise ValueError("Clause data precedes DIMACS header")
            if not CLAUSE_LINE.fullmatch(line.rstrip(b"\r\n")):
                raise ValueError("Require one clause per line, ASCII spaces and one final zero")
            for token in tokens[:-1]:
                literal = int(token)
                if abs(literal) > header[0]:
                    raise ValueError("Literal exceeds DIMACS variable bound")
            count += 1
    if header is None:
        raise ValueError("Missing DIMACS header")
    if count != header[1]:
        raise ValueError("Actual clause count differs from DIMACS header")
    if expected_variables is not None and header[0] != expected_variables:
        raise ValueError("DIMACS variables differ from generator MATCH")
    if expected_clauses is not None and count != expected_clauses:
        raise ValueError("DIMACS clauses differ from generator MATCH")
    return {"variables": header[0], "clauses": count, "bytes": size,
            "sha256": digest.hexdigest()}


def validate_emitter_match(path: Path, returncode: int, stdout: str) -> dict:
    """Require exactly one successful generator MATCH and matching strict DIMACS."""
    match = MATCH.fullmatch(stdout.strip())
    if returncode != 0 or match is None:
        raise ValueError("Generator check did not return a unique successful MATCH")
    clauses, variables = map(int, match.groups())
    return validate_dimacs(path, expected_variables=variables, expected_clauses=clauses)


def materialize_units(base: Path, base_sha256: str, units: list[int], output: Path,
                      expected_sha256: str, expected_bytes: int,
                      variables: int, clauses: int) -> dict:
    """Fresh owned output only; retain every non-header byte and ordered unit."""
    if not 0 < expected_bytes <= MAX_INPUT_BYTES:
        raise ValueError("Expected input exceeds the 99 MB bound")
    stats = validate_dimacs(base)
    if stats["sha256"] != base_sha256 or stats["variables"] != variables:
        raise ValueError("Base hash/variable identity mismatch")
    if any(type(x) is not int or x == 0 or abs(x) > variables for x in units):
        raise ValueError("Invalid signed unit literal")
    if clauses != stats["clauses"] + len(units):
        raise ValueError("Root clause count must include every ordered unit")
    digest = hashlib.sha256()
    size = 0
    source_digest = hashlib.sha256()
    with base.open("rb") as source, output.open("xb") as destination:
        def emit(data: bytes) -> None:
            nonlocal size
            if size + len(data) > MAX_INPUT_BYTES:
                raise ValueError("Generated input exceeds 99 MB bound")
            destination.write(data)
            digest.update(data)
            size += len(data)

        headers = 0
        while raw := source.readline(MAX_LINE_BYTES + 1):
            if len(raw) > MAX_LINE_BYTES:
                raise ValueError("Base line grew beyond bound")
            source_digest.update(raw)
            if raw.lstrip().startswith(b"p cnf"):
                headers += 1
                emit(f"p cnf {variables} {clauses}\n".encode())
            else:
                emit(raw)
        for literal in units:  # Duplicate units are intentionally retained.
            emit(f"{literal} 0\n".encode())
    if headers != 1 or source_digest.hexdigest() != base_sha256:
        raise ValueError("Base changed during materialization")
    if size != expected_bytes or digest.hexdigest() != expected_sha256:
        raise ValueError("Materialized bytes differ from the reviewed root identity")
    final = validate_dimacs(output, expected_variables=variables, expected_clauses=clauses)
    if final["sha256"] != expected_sha256:
        raise ValueError("Output changed during validation")
    return {"status": "materialized", "cnf_path": str(output.resolve()),
            "cnf_sha256": expected_sha256, "cnf_bytes": size,
            "variables": variables, "clauses": clauses,
            "base_sha256": base_sha256, "units": units, "output_created_exclusively": True}


def materialize_inventory_case(manifest_path: Path, manifest_sha256: str,
                               case_id: str, output: Path) -> dict:
    raw = manifest_path.read_bytes()
    if hashlib.sha256(raw).hexdigest() != manifest_sha256:
        raise ValueError("Sector inventory hash mismatch")
    inventory = json.loads(raw)
    schema = inventory.get("schema")
    if schema == "erdos85-phase-b-h5-inventory-v1":
        jobs = inventory["jobs"]
    elif schema == "erdos85-phase-b-h7-inventory-v1":
        jobs = inventory["survivors"]
    else:
        raise ValueError("Only the reviewed H5/H7 input recipes are supported")
    found = [row for row in jobs if row["id"] == case_id]
    if len(found) != 1:
        raise ValueError("Case ID is absent or duplicated in inventory")
    row = found[0]
    if schema == "erdos85-phase-b-h5-inventory-v1":
        base = inventory["bases"][row["cell"]]
        path, sha = base["base"], base["base_sha256"]
        variables, clauses = row["variables"], row["clauses"]
    else:
        base = inventory["base"]
        path, sha = base["path"], base["sha256"]
        variables, clauses = inventory["variables"], inventory["cube_clauses"]
    result = materialize_units((manifest_path.parent / path).resolve(), sha, row["units"],
                               output, row["cnf_sha256"], row["cnf_bytes"], variables, clauses)
    return dict(result, id=case_id, sector=row["sector"], manifest_sha256=manifest_sha256,
                generator=inventory["generator"])


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--manifest-sha256", required=True)
    parser.add_argument("--case-id", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    receipt = args.output.with_suffix(args.output.suffix + ".receipt.json")
    if args.output.exists() or receipt.exists():
        parser.error("Output and receipt must be new; retained inputs are never overwritten")
    result = materialize_inventory_case(args.manifest.resolve(), args.manifest_sha256,
                                        args.case_id, args.output.resolve())
    with receipt.open("x") as target:
        json.dump(result, target, indent=2)
        target.write("\n")
    print(json.dumps(result))


if __name__ == "__main__":
    main()
