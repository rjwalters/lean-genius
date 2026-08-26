#!/usr/bin/env python3
"""Generate the checked Lean module for the 66-job h7/t0 cube-one cover.

The input manifest is produced by ``generate_h7_t0_cube_one_cover_jobs.py``.
Every job must also have one accepted ledger row and one decompressed compact
LRAT payload.  Payload hashes and sizes are checked against the ledger before
any Lean source is emitted.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
from pathlib import Path


SCHEMA = "erdos85-h7-t0-cube1-cover-v1"
LEFT = [1254, 1288, 1322, 1356, 1390, 1424, 1458, 1492]
RIGHT = [1254, 1519, 1546, 1573, 1600, 1627, 1654, 1681]
JOB_RE = re.compile(
    r"h7_t0_cube1\.(?:cover-(?:left|right)|cube-([0-7])-([0-7]))")


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def materialized_identity(base: Path, variables: int, clauses: int,
                          units: list[int]) -> tuple[str, int]:
    """Hash the exact DIMACS bytes emitted by the checked job materializer."""
    digest = hashlib.sha256()
    size = 0
    replaced = False
    with base.open("rb") as source:
        for raw in source:
            if raw.lstrip().startswith(b"p cnf"):
                if replaced:
                    raise ValueError(f"duplicate DIMACS header: {base}")
                raw = f"p cnf {variables} {clauses + len(units)}\n".encode()
                replaced = True
            digest.update(raw)
            size += len(raw)
    if not replaced:
        raise ValueError(f"missing DIMACS header: {base}")
    for literal in units:
        raw = f"{literal} 0\n".encode()
        digest.update(raw)
        size += len(raw)
    return digest.hexdigest(), size


def payload_path(certificate_dir: Path, job_id: str) -> Path:
    candidates = (
        certificate_dir / f"{job_id}.lrat",
        certificate_dir / job_id / "job.lrat",
        certificate_dir / job_id / "proof.lrat",
    )
    for candidate in candidates:
        if candidate.is_file():
            return candidate.resolve()
    raise ValueError(f"missing decompressed LRAT for {job_id}: tried {candidates}")


def portable_include_paths(payloads: dict[str, Path], include_root: Path,
                           output: Path) -> dict[str, str]:
    """Return output-relative includes, rejecting payloads outside the bank root."""
    root = include_root.resolve()
    result = {}
    for job_id, payload in payloads.items():
        resolved = payload.resolve()
        try:
            resolved.relative_to(root)
        except ValueError as error:
            raise ValueError(
                f"LRAT payload is outside --include-root: {resolved}") from error
        result[job_id] = os.path.relpath(resolved, output.resolve().parent)
    return result


def read_accepted_ledger(path: Path) -> dict[str, dict[str, str]]:
    accepted: dict[str, dict[str, str]] = {}
    for line_number, line in enumerate(path.read_text().splitlines(), 1):
        fields = line.split()
        if len(fields) >= 4 and fields[2] == "UNSAT":
            job_id, metadata_fields = fields[1], fields[3:]
        elif len(fields) >= 3 and fields[1] == "UNSAT":
            job_id, metadata_fields = fields[0], fields[2:]
        else:
            continue
        values: dict[str, str] = {}
        for field in metadata_fields:
            if "=" in field:
                key, value = field.split("=", 1)
                values[key] = value
        if values.get("trim") != "VERIFIED" or values.get("upload") != "uploaded":
            continue
        if job_id in accepted:
            raise ValueError(f"duplicate accepted ledger row for {job_id}")
        if "lrat_sha256" not in values or "lrat_bytes" not in values:
            raise ValueError(f"{path}:{line_number}: incomplete accepted LRAT metadata")
        accepted[job_id] = values
    return accepted


def load_and_validate(
    manifest_path: Path, ledger_path: Path, certificate_dir: Path
) -> tuple[dict, dict[str, Path]]:
    manifest = json.loads(manifest_path.read_text())
    if manifest.get("schema") != SCHEMA:
        raise ValueError("unsupported h7 cube-one cover manifest schema")
    if manifest.get("left") != LEFT or manifest.get("right") != RIGHT:
        raise ValueError("manifest selectors differ from the checked Lean arrays")
    base = Path(manifest.get("base", ""))
    if not base.is_file() or sha256(base) != manifest.get("base_sha256"):
        raise ValueError("base CNF is missing or differs from the bound manifest hash")
    variables = manifest.get("variables")
    clauses = manifest.get("base_clauses")
    if variables != 30646 or clauses != 1330469:
        raise ValueError("unexpected h7/t0 cube-one base CNF shape")
    jobs = manifest.get("jobs")
    if not isinstance(jobs, list) or len(jobs) != 66:
        raise ValueError("expected exactly 66 h7 cube-one cover jobs")
    ids = [job.get("id") for job in jobs]
    if any(not isinstance(job_id, str) for job_id in ids) or len(set(ids)) != 66:
        raise ValueError("invalid or duplicate h7 cube-one job ids")
    expected = {
        "h7_t0_cube1.cover-left", "h7_t0_cube1.cover-right",
        *(f"h7_t0_cube1.cube-{left}-{right}"
          for left in range(8) for right in range(8)),
    }
    if set(ids) != expected:
        raise ValueError("h7 cube-one manifest does not contain the exact 8-by-8 cover")
    for job in jobs:
        match = JOB_RE.fullmatch(job["id"])
        if match is None:
            raise ValueError(f"malformed job id: {job['id']}")
        if job["id"].endswith("cover-left"):
            if job.get("kind") != "cover-left" or job.get("units") != [
                -literal for literal in manifest["left"]]:
                raise ValueError("left cover units disagree with manifest selectors")
        elif job["id"].endswith("cover-right"):
            if job.get("kind") != "cover-right" or job.get("units") != [
                -literal for literal in manifest["right"]]:
                raise ValueError("right cover units disagree with manifest selectors")
        else:
            left, right = map(int, match.groups())
            if (job.get("kind") != "cube" or
                    job.get("left_index") != left or
                    job.get("right_index") != right or
                    job.get("units") != [manifest["left"][left],
                                         manifest["right"][right]]):
                raise ValueError(f"cube metadata mismatch: {job['id']}")

    accepted = read_accepted_ledger(ledger_path)
    missing = expected - set(accepted)
    unexpected = set(accepted) - expected
    if missing or unexpected:
        raise ValueError(
            f"ledger coverage mismatch: missing={sorted(missing)}, "
            f"unexpected={sorted(unexpected)}")
    payloads: dict[str, Path] = {}
    for job_id in sorted(expected):
        payload = payload_path(certificate_dir, job_id)
        metadata = accepted[job_id]
        job = next(record for record in jobs if record["id"] == job_id)
        cnf_hash, cnf_bytes = materialized_identity(
            base, variables, clauses, job["units"])
        if (metadata.get("emitted_cnf_sha256") != cnf_hash or
                metadata.get("solved_cnf_sha256") != cnf_hash or
                int(metadata.get("cnf_bytes", -1)) != cnf_bytes or
                int(metadata.get("maxvar", -1)) != variables):
            raise ValueError(f"materialized CNF identity mismatch for {job_id}")
        if payload.stat().st_size != int(metadata["lrat_bytes"]):
            raise ValueError(f"LRAT size mismatch for {job_id}")
        if sha256(payload) != metadata["lrat_sha256"]:
            raise ValueError(f"LRAT hash mismatch for {job_id}")
        payloads[job_id] = payload
    return manifest, payloads


def lean_stem(job_id: str) -> str:
    words = re.split(r"[^A-Za-z0-9]+", job_id)
    return "h7CubeOne" + "".join(word[:1].upper() + word[1:] for word in words)


def cnf_expression(job: dict) -> str:
    kind = job["kind"]
    if kind == "cover-left":
        return "sevenHighT0CubeOneLeftCoverCnf"
    if kind == "cover-right":
        return "sevenHighT0CubeOneRightCoverCnf"
    left, right = job["left_index"], job["right_index"]
    return ("sevenHighT0CubeOnePositiveCnf "
            f"sevenHighT0CubeOneLeftVariables[{left}] "
            f"sevenHighT0CubeOneRightVariables[{right}]")


def render(manifest: dict, payloads: dict[str, str]) -> str:
    lines = [
        "import Proofs.Erdos85OrderFortyNineSevenHighT0CubeOneCover",
        "import Proofs.Erdos85OrderFortyNineLratCertificateBase", "",
        "/-! GENERATED checked certificates for the h7/t0 cube-one cover. -/",
        "", "namespace Erdos85", "", "open Std Sat Std.Tactic.BVDecide", "",
    ]
    for job in manifest["jobs"]:
        job_id = job["id"]
        stem = lean_stem(job_id)
        cnf = cnf_expression(job)
        lines.extend([
            f"private def {stem}Proof : Array LRAT.IntAction :=",
            "  parseOrderFortyNineLratProof",
            f"    (include_str {json.dumps(payloads[job_id])})", "",
            "set_option maxHeartbeats 0 in",
            "set_option maxRecDepth 1000000 in",
            f"private theorem {stem}Check : LRAT.check {stem}Proof ({cnf}) := by",
            "  native_decide", "",
            f"private theorem {stem}Unsat : ({cnf}).Unsat :=",
            f"  LRAT.check_sound _ _ {stem}Check", "",
        ])
    lines.extend([
        "theorem sevenHighT0CubeOneCertificateGrid :",
        "    SevenHighT0CubeOneCheckedGrid := by",
        "  refine ⟨h7CubeOneH7T0Cube1CoverLeftUnsat,",
        "    h7CubeOneH7T0Cube1CoverRightUnsat, ?_⟩",
        "  intro left right",
        "  fin_cases left <;> fin_cases right",
    ])
    for left in range(8):
        for right in range(8):
            lines.append(
                f"  · exact {lean_stem(f'h7_t0_cube1.cube-{left}-{right}')}Unsat")
    lines.extend([
        "", "/-- Checked exclusion of the last canonical h7/t0 representative. -/",
        "theorem sevenHighT0_canonicalExcluded_of_cubeOne_certificates :",
        "    SevenHighCanonicalRepresentativeExcluded 0 0 :=",
        "  sevenHighT0_canonicalExcluded_of_cubeOne_checkedGrid",
        "    sevenHighT0CubeOneCertificateGrid", "", "end Erdos85", "",
        "#print axioms Erdos85.sevenHighT0_canonicalExcluded_of_cubeOne_certificates",
        "",
    ])
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--ledger", type=Path, required=True)
    parser.add_argument("--certificate-dir", type=Path, required=True)
    parser.add_argument(
        "--include-root", type=Path, required=True,
        help="portable certificate root that must contain every LRAT payload")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    manifest, payloads = load_and_validate(
        args.manifest, args.ledger, args.certificate_dir)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    includes = portable_include_paths(payloads, args.include_root, args.output)
    args.output.write_text(render(manifest, includes))
    print(f"WROTE {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
