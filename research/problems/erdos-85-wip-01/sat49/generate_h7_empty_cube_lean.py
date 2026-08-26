#!/usr/bin/env python3
"""Generate the mixed direct/binary-split H7 empty-cube Lean provider."""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import os
import re
from pathlib import Path

import generate_h7_empty_cube_manifest as parents
import generate_h7_empty_cube_split_jobs as splits


RECEIPT_RE = re.compile(
    r"(cube_F(\d+)_t(\d+)\.split-([01]))\s+"
    r"([0-9a-f]{64})\s+([0-9a-f]{64})\s+(\d+)$")
COUNTS = {6: 19, 7: 15, 8: 7, 9: 2}


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def read_split_receipts(path: Path) -> dict[str, dict[str, object]]:
    result = {}
    for number, raw in enumerate(path.read_text().splitlines(), 1):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        match = RECEIPT_RE.fullmatch(line)
        if match is None:
            raise ValueError(f"{path}:{number}: malformed split receipt")
        job_id, edge_count, type_index, value, cnf_hash, proof_hash, size = match.groups()
        record = {
            "edge_count": int(edge_count), "type_index": int(type_index),
            "value": int(value), "cnf_sha256": cnf_hash,
            "lrat_gz_sha256": proof_hash, "lrat_gz_bytes": int(size),
        }
        if job_id in result:
            raise ValueError(f"duplicate split receipt: {job_id}")
        result[job_id] = record
    return result


def _gzip_payload(directory: Path, job_id: str, metadata: dict) -> Path:
    payload = directory / f"{job_id}.lrat.gz"
    if not payload.is_file():
        raise ValueError(f"missing compressed LRAT: {payload}")
    if (payload.stat().st_size != metadata["lrat_gz_bytes"] or
            sha256(payload) != metadata["lrat_gz_sha256"]):
        raise ValueError(f"compressed LRAT identity mismatch: {job_id}")
    return payload


def _unpack(payload: Path, destination: Path) -> None:
    destination.parent.mkdir(parents=True, exist_ok=True)
    temporary = destination.with_name(f".{destination.name}.tmp")
    with gzip.open(payload, "rb") as source, temporary.open("wb") as target:
        for chunk in iter(lambda: source.read(1 << 20), b""):
            target.write(chunk)
    os.replace(temporary, destination)


def validate_and_unpack(parent_manifest: dict, split_manifest: dict,
                        split_receipts: dict[str, dict[str, object]],
                        base: Path,
                        direct_dir: Path, split_dir: Path,
                        proof_dir: Path) -> tuple[list[dict], dict[str, Path]]:
    if parent_manifest.get("schema") != parents.SCHEMA:
        raise ValueError("unsupported parent manifest schema")
    if split_manifest.get("schema") != splits.SCHEMA:
        raise ValueError("unsupported split manifest schema")
    if (split_manifest.get("base_sha256") != parent_manifest.get("base_sha256") or
            split_manifest.get("variables") != parent_manifest.get("variables") or
            split_manifest.get("base_clauses") != parent_manifest.get("base_clauses")):
        raise ValueError("split manifest is not bound to the parent base")
    jobs = parent_manifest.get("jobs")
    if not isinstance(jobs, list) or len(jobs) != 43:
        raise ValueError("parent manifest must contain exactly 43 jobs")
    expected_ids = {f"cube_F{f}_t{i}" for f, count in COUNTS.items()
                    for i in range(count)}
    if {job.get("id") for job in jobs} != expected_ids:
        raise ValueError("parent manifest inventory differs from 19/15/7/2")
    direct = {job["id"]: job for job in jobs if job.get("status") == "certified"}
    missing = {job["id"]: job for job in jobs if job.get("status") == "missing"}
    if len(direct) + len(missing) != 43:
        raise ValueError("parent status must be certified or missing")
    split_records = split_manifest.get("splits")
    if not isinstance(split_records, list) or {
            record.get("parent_id") for record in split_records} != set(missing):
        raise ValueError("split manifest must cover exactly the missing parents")

    evidence = []
    payloads = {}
    for job in jobs:
        job_id = job["id"]
        if job_id in direct:
            payload = _gzip_payload(direct_dir, job_id, job)
            unpacked = proof_dir / f"{job_id}.lrat"
            _unpack(payload, unpacked)
            payloads[job_id] = unpacked.resolve()
            evidence.append({**job, "kind": "direct"})
            continue
        record = next(item for item in split_records if item["parent_id"] == job_id)
        variable = record.get("split_variable")
        if not isinstance(variable, int) or variable <= 0:
            raise ValueError(f"invalid one-based split variable: {job_id}")
        leaves = record.get("leaves")
        expected_leaf_ids = {f"{job_id}.split-0", f"{job_id}.split-1"}
        if (not isinstance(leaves, list) or
                {leaf.get("id") for leaf in leaves} != expected_leaf_ids):
            raise ValueError(f"non-exhaustive split leaves: {job_id}")
        for leaf in leaves:
            leaf_id = leaf["id"]
            receipt = split_receipts.get(leaf_id)
            if receipt is None:
                raise ValueError(f"missing accepted split receipt: {leaf_id}")
            value = int(bool(leaf.get("value")))
            if (receipt["edge_count"] != job["edge_count"] or
                    receipt["type_index"] != job["type_index"]):
                raise ValueError(f"split receipt parent mismatch: {leaf_id}")
            expected_units = [*job["units"], variable if value else -variable]
            if leaf.get("units") != expected_units or receipt["value"] != value:
                raise ValueError(f"split polarity/unit mismatch: {leaf_id}")
            prefix_hash, _ = _leaf_identity(parent_manifest, base, expected_units)
            if receipt["cnf_sha256"] != prefix_hash:
                raise ValueError(f"split CNF receipt mismatch: {leaf_id}")
            payload = _gzip_payload(split_dir, leaf_id, receipt)
            unpacked = proof_dir / f"{leaf_id}.lrat"
            _unpack(payload, unpacked)
            payloads[leaf_id] = unpacked.resolve()
        evidence.append({**job, "kind": "binarySplit", "split_variable": variable})
    if set(split_receipts) != {leaf_id for job_id in missing
                              for leaf_id in (f"{job_id}.split-0",
                                              f"{job_id}.split-1")}:
        raise ValueError("split receipt inventory has missing or surplus leaves")
    return evidence, payloads


def _leaf_identity(parent_manifest: dict, base: Path,
                   units: list[int]) -> tuple[str, int]:
    if not base.is_file() or parents.sha256(base) != parent_manifest.get("base_sha256"):
        raise ValueError("parent manifest base path/hash unavailable")
    digest = hashlib.sha256()
    size = 0
    with base.open("rb") as stream:
        for raw in stream:
            if raw.lstrip().startswith(b"p cnf"):
                raw = f"p cnf {parents.VARIABLES} {parents.BASE_CLAUSES + len(units)}\n".encode()
            digest.update(raw)
            size += len(raw)
    for literal in units:
        raw = f"{literal} 0\n".encode()
        digest.update(raw)
        size += len(raw)
    return digest.hexdigest(), size


def lean_stem(job_id: str) -> str:
    return "h7Empty" + "".join(
        word[:1].upper() + word[1:] for word in re.split(r"[^A-Za-z0-9]+", job_id))


def render(evidence: list[dict], includes: dict[str, str]) -> str:
    lines = [
        "import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalEmptyCubeSplitTerminal",
        "import Proofs.Erdos85OrderFortyNineLratCertificateBase", "",
        "/-! GENERATED checked evidence for all 43 canonical H7 empty cubes. -/", "",
        "namespace Erdos85", "", "open Std Sat Std.Tactic.BVDecide", "",
    ]
    for job in evidence:
        ids = ([job["id"]] if job["kind"] == "direct" else
               [f'{job["id"]}.split-0', f'{job["id"]}.split-1'])
        for proof_id in ids:
            stem = lean_stem(proof_id)
            if proof_id == job["id"]:
                cnf = ("orderFortyNineSevenHighT0CanonicalEmptyCubeSatCnf "
                       f"{job['edge_count']} {job['type_index']}")
            else:
                value = "true" if proof_id.endswith("1") else "false"
                cnf = ("orderFortyNineSevenHighT0CanonicalEmptyCubeSplitSatCnf "
                       f"{job['edge_count']} {job['type_index']} "
                       f"{job['split_variable'] - 1} {value}")
            lines += [
                f"private def {stem}Proof : Array LRAT.IntAction :=",
                "  parseOrderFortyNineLratProof",
                f"    (include_str {json.dumps(includes[proof_id])})", "",
                "set_option maxHeartbeats 0 in", "set_option maxRecDepth 1000000 in",
                f"private theorem {stem}Check : LRAT.check {stem}Proof ({cnf}) := by",
                "  native_decide", "",
            ]
    by_key = {(job["edge_count"], job["type_index"]): job for job in evidence}
    for edge_count, count in COUNTS.items():
        lines += [f"private def h7EmptyEvidenceF{edge_count} : ∀ i : Fin {count},",
                  "    SevenHighT0CanonicalEmptyCubeLratEvidence "
                  f"{edge_count} i := by", "  intro i", "  fin_cases i"]
        for index in range(count):
            job = by_key[(edge_count, index)]
            if job["kind"] == "direct":
                stem = lean_stem(job["id"])
                lines.append(f"  · exact .direct {stem}Proof {stem}Check")
            else:
                false_stem = lean_stem(f'{job["id"]}.split-0')
                true_stem = lean_stem(f'{job["id"]}.split-1')
                lines.append(
                    f"  · exact .binarySplit {job['split_variable'] - 1} "
                    f"{false_stem}Proof {true_stem}Proof "
                    f"{false_stem}Check {true_stem}Check")
        lines.append("")
    lines += [
        "theorem sevenHighT0CanonicalEmptyCubeCheckedProvider :",
        "    SevenHighT0CanonicalEmptyCubeCheckedProvider :=",
        "  sevenHighT0CanonicalEmptyCubeCheckedProvider_of_evidenceVectors",
        "    h7EmptyEvidenceF6 h7EmptyEvidenceF7 h7EmptyEvidenceF8 h7EmptyEvidenceF9",
        "", "end Erdos85", "",
        "#print axioms Erdos85.sevenHighT0CanonicalEmptyCubeCheckedProvider", "",
    ]
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--parent-manifest", type=Path, required=True)
    parser.add_argument("--split-manifest", type=Path, required=True)
    parser.add_argument("--base", type=Path, required=True)
    parser.add_argument("--split-receipts", type=Path, required=True)
    parser.add_argument("--direct-certificate-dir", type=Path, required=True)
    parser.add_argument("--split-certificate-dir", type=Path, required=True)
    parser.add_argument("--proof-output-dir", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    parent = json.loads(args.parent_manifest.read_text())
    split = json.loads(args.split_manifest.read_text())
    if split.get("parent_manifest_sha256") != sha256(args.parent_manifest):
        raise ValueError("split manifest parent hash mismatch")
    evidence, payloads = validate_and_unpack(
        parent, split, read_split_receipts(args.split_receipts), args.base,
        args.direct_certificate_dir, args.split_certificate_dir,
        args.proof_output_dir)
    includes = {key: os.path.relpath(path, args.output.resolve().parent)
                for key, path in payloads.items()}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(render(evidence, includes))
    print(f"WROTE {args.output} (43 parents, {len(payloads)} LRAT leaves)")


if __name__ == "__main__":
    main()
