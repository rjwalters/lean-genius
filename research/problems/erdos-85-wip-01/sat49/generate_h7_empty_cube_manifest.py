#!/usr/bin/env python3
"""Bind the canonical H7 empty-cube campaign to exact CNF/LRAT identities."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path

import check_h7_t0_by_empty_graph as cubes
import check_h7_t0_canonical_completion as canonical


SCHEMA = "erdos85-h7-canonical-empty-cubes-v1"
BASE_SHA256 = "8bc9b8f15b7f03194f39d208b2c0015e6039e0aac759ccfce0b6415724130eb0"
VARIABLES = 17633
BASE_CLAUSES = 720804
CERT_RE = re.compile(
    r"compactcube F=(\d+) type=(\d+) UNSAT_CERT .*?"
    r"cnf_sha=([0-9a-f]{64}) .*?lrat_gz_sha=([0-9a-f]{64}) "
    r"lrat_gz_bytes=(\d+)$")
RECEIPT_TSV_RE = re.compile(
    r"cube_F(\d+)_t(\d+)\s+([0-9a-f]{64})\s+([0-9a-f]{64})\s+(\d+)$")


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def inspect_base(path: Path) -> tuple[hashlib._Hash, int]:
    """Return a hash state for the cube header+base body and its byte count."""
    digest = hashlib.sha256()
    size = 0
    header_seen = False
    with path.open("rb") as stream:
        for raw in stream:
            if raw.lstrip().startswith(b"p cnf"):
                if header_seen:
                    raise ValueError("duplicate DIMACS header")
                raw = f"p cnf {VARIABLES} {BASE_CLAUSES + 21}\n".encode()
                header_seen = True
            digest.update(raw)
            size += len(raw)
    if not header_seen:
        raise ValueError("missing DIMACS header")
    return digest, size


def cube_identity(prefix: hashlib._Hash, prefix_bytes: int,
                  units: list[int]) -> tuple[str, int]:
    digest = prefix.copy()
    size = prefix_bytes
    for literal in units:
        raw = f"{literal} 0\n".encode()
        digest.update(raw)
        size += len(raw)
    return digest.hexdigest(), size


def accepted_receipts(path: Path) -> dict[tuple[int, int], dict[str, object]]:
    receipts: dict[tuple[int, int], dict[str, object]] = {}
    for line in path.read_text().splitlines():
        match = CERT_RE.search(line)
        if match is None:
            match = RECEIPT_TSV_RE.fullmatch(line.strip())
        if match is None and line.lstrip().startswith("cube_F"):
            raise ValueError(f"malformed canonical receipt row: {line!r}")
        if match is None:
            continue
        edge_count, type_index, cnf_hash, proof_hash, proof_bytes = match.groups()
        key = (int(edge_count), int(type_index))
        receipt = {
            "cnf_sha256": cnf_hash,
            "lrat_gz_sha256": proof_hash,
            "lrat_gz_bytes": int(proof_bytes),
        }
        previous = receipts.get(key)
        if previous is not None and previous != receipt:
            raise ValueError(f"conflicting accepted receipts for F={key[0]} t={key[1]}")
        receipts[key] = receipt
    return receipts


def build_manifest(base: Path, ledger: Path, certificate_dir: Path) -> dict:
    if sha256(base) != BASE_SHA256:
        raise ValueError("compact base CNF hash mismatch")
    prefix, prefix_bytes = inspect_base(base)
    receipts = accepted_receipts(ledger)
    _, edge_variables, _ = canonical.build_cnf()
    jobs = []
    expected = set()
    for edge_count in range(6, 10):
        representatives = cubes.graph_representatives(edge_count)
        for type_index, mask in enumerate(representatives):
            key = (edge_count, type_index)
            expected.add(key)
            units = []
            for index, (left, right) in enumerate(cubes.quotient.EDGES):
                variable = edge_variables[(7 + left, 7 + right)]
                units.append(variable if (mask >> index) & 1 else -variable)
            cnf_hash, cnf_bytes = cube_identity(prefix, prefix_bytes, units)
            job = {
                "id": f"cube_F{edge_count}_t{type_index}",
                "edge_count": edge_count,
                "type_index": type_index,
                "mask": mask,
                "units": units,
                "cnf_sha256": cnf_hash,
                "cnf_bytes": cnf_bytes,
                "status": "missing",
            }
            receipt = receipts.get(key)
            if receipt is not None:
                if receipt["cnf_sha256"] != cnf_hash:
                    raise ValueError(f"CNF receipt mismatch for {job['id']}")
                proof = certificate_dir / f"{job['id']}.lrat.gz"
                if not proof.is_file():
                    raise ValueError(f"missing accepted payload: {proof}")
                if (proof.stat().st_size != receipt["lrat_gz_bytes"] or
                        sha256(proof) != receipt["lrat_gz_sha256"]):
                    raise ValueError(f"LRAT payload identity mismatch for {job['id']}")
                job.update(status="certified", certificate=proof.name, **receipt)
            jobs.append(job)
    unexpected = set(receipts) - expected
    if unexpected:
        raise ValueError(f"accepted receipts outside the 43-cube inventory: {unexpected}")
    return {
        "schema": SCHEMA,
        "identifier_convention": "one-based signed DIMACS",
        "base_sha256": BASE_SHA256,
        "variables": VARIABLES,
        "base_clauses": BASE_CLAUSES,
        "cube_clauses": BASE_CLAUSES + 21,
        "representative_counts": [19, 15, 7, 2],
        "job_count": len(jobs),
        "certified_count": sum(job["status"] == "certified" for job in jobs),
        "jobs": jobs,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base", type=Path, required=True)
    parser.add_argument("--ledger", type=Path, required=True)
    parser.add_argument("--certificate-dir", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    manifest = build_manifest(args.base, args.ledger, args.certificate_dir)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    print(f"WROTE {args.output} ({manifest['certified_count']}/{manifest['job_count']} certified)")


if __name__ == "__main__":
    main()
