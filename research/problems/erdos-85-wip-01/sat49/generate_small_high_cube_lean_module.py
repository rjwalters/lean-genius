#!/usr/bin/env python3
"""Generate the Lean certificate module for the seven small-high cube grids.

The input is the exact manifest emitted by ``generate_small_high_cube_jobs``.
Each job must have a corresponding *decompressed* compact text LRAT, either
named ``<job id>.lrat`` or stored under the worker's ``<job id>/job.lrat``
layout.  Lean's ``include_str`` cannot consume the uploaded ``.lrat.gz``
directly.
The generated module checks every payload and assembles the 406 results into
seven ``OrderFortyNineSmallHighCheckedCubeGrid`` values.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
from pathlib import Path

APPROVED_ROOT_MANIFEST_SHA256 = "05381a1cf5e80eb480b6e78c4a8dada2573c1cf2f0c55d9ac0bcc4367e3bca76"
APPROVED_ROOT_COMMIT = "38b15d484b22d205476baba9f4898c9ffc91044d"
APPROVED_FREIGHT_RECEIPT_SHA256 = "6084315bc86ad262533a660aad308639d1d087666b965df47569627c6adf2897"
PAYLOAD_SCHEMA = "erdos85-small-high-decompressed-payloads-v1"
MODULE_RECEIPT_SCHEMA = "erdos85-small-high-generated-module-v1"
SOURCE_MODULE = "Proofs.Generated.Erdos85OrderFortyNineSmallHighCertificates"


CELL_LEAN = {
    "h3_b1": (
        "orderFortyNineGeneratedThreeHighDistOneB1ScoutCnf",
        "orderFortyNineThreeHighDistOneNoCoincidenceMasks", "three"),
    "h3_c1": (
        "orderFortyNineGeneratedThreeHighDistOneC1ScoutCnf",
        "orderFortyNineThreeHighDistOneNoCoincidenceMasks", "three"),
    "h3_c2": (
        "orderFortyNineGeneratedThreeHighDistOneC2ScoutCnf",
        "orderFortyNineThreeHighDistOneC2Masks", "three"),
    "h3_dist2": (
        "orderFortyNineGeneratedThreeHighDistTwoScoutCnf",
        "orderFortyNineThreeHighDistTwoMasks", "three"),
    "h5_t0": (
        "orderFortyNineGeneratedVariableHighSatCnf (5 : Fin 50) orderFortyNineFiveHighT0Masks",
        "orderFortyNineFiveHighT0Masks", "five"),
    "h5_t1": (
        "orderFortyNineGeneratedVariableHighSatCnf (5 : Fin 50) orderFortyNineFiveHighT1Masks",
        "orderFortyNineFiveHighT1Masks", "five"),
    "h5_t2": (
        "orderFortyNineGeneratedVariableHighSatCnf (5 : Fin 50) orderFortyNineFiveHighT2Masks",
        "orderFortyNineFiveHighT2Masks", "five"),
}


def lean_stem(job_id: str) -> str:
    words = re.split(r"[^A-Za-z0-9]+", job_id)
    return "smallHigh" + "".join(word[:1].upper() + word[1:] for word in words)


def payload_path(certificate_dir: Path, job_id: str) -> Path:
    """Accept either the upload's flat layout or the worker's job directory."""
    candidates = [certificate_dir / f"{job_id}.lrat",
                  certificate_dir / job_id / "job.lrat",
                  certificate_dir / job_id / "proof.lrat"]
    for candidate in candidates:
        if candidate.is_file():
            return candidate.resolve()
    raise ValueError(f"missing LRAT payload for {job_id}: tried {candidates}")


def canonical(value: object) -> bytes:
    return (json.dumps(value, ensure_ascii=True, allow_nan=False,
                       sort_keys=True, separators=(",", ":")) + "\n").encode("ascii")


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def require_regular(path: Path, label: str) -> None:
    if not path.is_absolute() or path.is_symlink() or not path.is_file():
        raise ValueError(f"{label} must be an absolute regular non-symlink file")


def portable_include_path(payload: Path, include_root: Path,
                          output: Path) -> str:
    root = include_root.resolve()
    resolved = payload.resolve()
    try:
        resolved.relative_to(root)
    except ValueError as error:
        raise ValueError(
            f"LRAT payload is outside --include-root: {resolved}") from error
    return os.path.relpath(resolved, output.resolve().parent)


def load_and_validate(manifest_path: Path, certificate_dir: Path) -> dict:
    manifest = json.loads(manifest_path.read_text())
    if manifest.get("schema") != "erdos85-small-high-cube-jobs-v1":
        raise ValueError("unsupported cube-job manifest schema")
    cells = manifest.get("cells")
    if not isinstance(cells, dict) or set(cells) != set(CELL_LEAN):
        raise ValueError("manifest must contain exactly the seven checked cells")
    seen: set[str] = set()
    for cell_name, cell in cells.items():
        jobs = cell.get("jobs")
        if not isinstance(jobs, list) or len(jobs) != 58:
            raise ValueError(f"{cell_name}: expected 58 jobs")
        kinds = [job.get("kind") for job in jobs]
        if kinds.count("cover-left") != 1 or kinds.count("cover-right") != 1:
            raise ValueError(f"{cell_name}: malformed cover jobs")
        cubes = {(job.get("left_index"), job.get("right_index"))
                 for job in jobs if job.get("kind") == "cube"}
        if cubes != {(li, ri) for li in range(7) for ri in range(8)}:
            raise ValueError(f"{cell_name}: incomplete 7-by-8 cube grid")
        for job in jobs:
            job_id = job.get("id")
            if not isinstance(job_id, str) or job_id in seen:
                raise ValueError(f"duplicate or invalid job id: {job_id!r}")
            seen.add(job_id)
            payload_path(certificate_dir, job_id)
    if len(seen) != 406:
        raise ValueError(f"expected 406 jobs, found {len(seen)}")
    return manifest


def validate_production_inputs(manifest_path: Path, manifest_sha256: str,
                               certificate_dir: Path, include_root: Path,
                               payload_manifest_path: Path,
                               payload_manifest_sha256: str) -> tuple[dict, list[dict]]:
    require_regular(manifest_path, "root manifest")
    require_regular(payload_manifest_path, "payload manifest")
    for directory, label in ((certificate_dir, "certificate directory"),
                             (include_root, "include root")):
        if not directory.is_absolute() or directory.is_symlink() or not directory.is_dir():
            raise ValueError(f"{label} must be an absolute real non-symlink directory")
    if manifest_sha256 != APPROVED_ROOT_MANIFEST_SHA256 or sha256(manifest_path) != manifest_sha256:
        raise ValueError("root manifest differs from the approved SHA")
    manifest = load_and_validate(manifest_path, certificate_dir)
    if (manifest_path.read_bytes() != canonical(manifest)
            or manifest.get("lean_commit") != APPROVED_ROOT_COMMIT
            or manifest.get("freight_receipt_sha256") != APPROVED_FREIGHT_RECEIPT_SHA256):
        raise ValueError("root manifest lineage/canonical bytes mismatch")
    if sha256(payload_manifest_path) != payload_manifest_sha256:
        raise ValueError("payload manifest SHA mismatch")
    raw = payload_manifest_path.read_bytes()
    document = json.loads(raw)
    if (not isinstance(document, dict) or set(document) != {
            "schema", "root_manifest_sha256", "payloads"}
            or raw != canonical(document) or document["schema"] != PAYLOAD_SCHEMA
            or document["root_manifest_sha256"] != manifest_sha256
            or not isinstance(document["payloads"], list)):
        raise ValueError("payload manifest schema/canonical bytes mismatch")
    expected_jobs = [job["id"] for cell in CELL_LEAN
                     for job in manifest["cells"][cell]["jobs"]]
    rows = document["payloads"]
    if [row.get("job_id") for row in rows if isinstance(row, dict)] != expected_jobs:
        raise ValueError("payload manifest is not the exact ordered 406-job set")
    for row, job_id in zip(rows, expected_jobs, strict=True):
        if set(row) != {"job_id", "path", "sha256"}:
            raise ValueError(f"{job_id}: invalid payload identity fields")
        path = Path(row["path"])
        require_regular(path, f"{job_id} payload")
        if path.resolve() != payload_path(certificate_dir, job_id):
            raise ValueError(f"{job_id}: payload path differs from worker layout")
        try: path.resolve().relative_to(include_root.resolve())
        except ValueError as error: raise ValueError(f"{job_id}: payload is outside include root") from error
        if not re.fullmatch(r"[0-9a-f]{64}", str(row["sha256"])) or sha256(path) != row["sha256"]:
            raise ValueError(f"{job_id}: payload SHA mismatch")
    return manifest, rows


def atomic_create(path: Path, raw: bytes) -> None:
    if not path.parent.is_dir() or path.parent.is_symlink():
        raise ValueError("output parent must already be a real non-symlink directory")
    temporary = path.with_name(f".{path.name}.tmp.{os.getpid()}")
    try:
        with temporary.open("xb") as stream:
            stream.write(raw); stream.flush(); os.fsync(stream.fileno())
        os.link(temporary, path)
        descriptor = os.open(path.parent, os.O_RDONLY)
        try: os.fsync(descriptor)
        finally: os.close(descriptor)
    finally:
        temporary.unlink(missing_ok=True)


def cnf_expression(cell_name: str, job: dict) -> str:
    base, masks, family = CELL_LEAN[cell_name]
    left = f"orderFortyNine{family.title()}HighCubeLeftVariables {masks}"
    right = f"orderFortyNine{family.title()}HighCubeRightVariables {masks}"
    kind = job["kind"]
    if kind == "cover-left":
        return f"orderFortyNineSmallHighLeftCoverCnf ({base}) ({left})"
    if kind == "cover-right":
        return f"orderFortyNineSmallHighRightCoverCnf ({base}) ({right})"
    li, ri = job["left_index"], job["right_index"]
    return ("orderFortyNineSmallHighPositiveCubeCnf "
            f"({base}) ({left})[{li}] ({right})[{ri}]")


def render(manifest: dict, certificate_dir: Path,
           include_root: Path, output: Path) -> str:
    lines = [
        "import Proofs.Erdos85OrderFortyNineSmallHighCubeGridTerminal",
        "import Proofs.Erdos85OrderFortyNineLratCertificateBase", "",
        "/-! Generated checked certificates for the 406 small-high cube jobs. -/",
        "", "namespace Erdos85", "", "open Std Sat Std.Tactic.BVDecide", "",
    ]
    for cell_name in CELL_LEAN:
        for job in manifest["cells"][cell_name]["jobs"]:
            stem = lean_stem(job["id"])
            payload = portable_include_path(
                payload_path(certificate_dir, job["id"]), include_root, output)
            cnf = cnf_expression(cell_name, job)
            lines.extend([
                f"def {stem}Proof : Array LRAT.IntAction :=",
                "  parseOrderFortyNineLratProof",
                f"    (include_str {json.dumps(payload)})", "",
                "set_option maxHeartbeats 0 in",
                "set_option maxRecDepth 1000000 in",
                f"theorem {stem}_check : LRAT.check {stem}Proof ({cnf}) := by",
                "  native_decide", "",
                f"theorem {stem}_unsat : ({cnf}).Unsat :=",
                f"  LRAT.check_sound _ _ {stem}_check", "",
            ])
    for cell_name, (base, masks, family) in CELL_LEAN.items():
        left = f"orderFortyNine{family.title()}HighCubeLeftVariables {masks}"
        right = f"orderFortyNine{family.title()}HighCubeRightVariables {masks}"
        cell_stem = lean_stem(cell_name)
        left_stem = lean_stem(f"{cell_name}.cover-left")
        right_stem = lean_stem(f"{cell_name}.cover-right")
        lines.extend([
            f"theorem {cell_stem}Grid :",
            f"    OrderFortyNineSmallHighCheckedCubeGrid ({base}) ({left}) ({right}) := by",
            "  refine ⟨?_, ?_, ?_⟩",
            f"  · exact {left_stem}_unsat",
            f"  · exact {right_stem}_unsat",
            "  · intro li ri",
            "    fin_cases li <;> fin_cases ri",
        ])
        for li in range(7):
            for ri in range(8):
                lines.append(f"    · exact {lean_stem(f'{cell_name}.cube-{li}-{ri}')}_unsat")
        lines.extend(["", f"theorem {cell_stem}Base_unsat : ({base}).Unsat :=",
                      "  orderFortyNineSmallHigh_unsat_of_checkedCubeGrid "
                      f"{cell_stem}Grid", ""])
    lines.extend([
        "theorem orderFortyNineStratumExcluded_three_of_cubeCertificates :",
        "    OrderFortyNineStratumExcluded 3 :=",
        "  orderFortyNineStratumExcluded_three_of_cubeBaseUnsat",
        "    smallHighH3B1Base_unsat smallHighH3C1Base_unsat",
        "    smallHighH3C2Base_unsat smallHighH3Dist2Base_unsat", "",
        "theorem orderFortyNineStratumExcluded_five_of_cubeCertificates :",
        "    OrderFortyNineStratumExcluded 5 :=",
        "  orderFortyNineStratumExcluded_five_of_cubeBaseUnsat",
        "    smallHighH5T0Base_unsat smallHighH5T1Base_unsat",
        "    smallHighH5T2Base_unsat", "",
    ])
    lines.extend(["end Erdos85", ""])
    return "\n".join(lines)


def main() -> int:
    generator_sha256 = sha256(Path(__file__))
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--manifest-sha256", required=True)
    parser.add_argument("--certificate-dir", type=Path, required=True)
    parser.add_argument("--payload-manifest", type=Path, required=True)
    parser.add_argument("--payload-manifest-sha256", required=True)
    parser.add_argument(
        "--include-root", type=Path, required=True,
        help="portable certificate root that must contain every LRAT payload")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    manifest, payloads = validate_production_inputs(
        args.manifest, args.manifest_sha256, args.certificate_dir,
        args.include_root, args.payload_manifest, args.payload_manifest_sha256)
    if not args.output.is_absolute() or args.output.is_symlink():
        parser.error("--output must be an absolute absent non-symlink path")
    receipt_path = Path(str(args.output) + ".receipt.json")
    if os.path.lexists(args.output) or os.path.lexists(receipt_path):
        parser.error("output module and receipt must both be absent")
    source = render(
        manifest, args.certificate_dir.resolve(), args.include_root.resolve(),
        args.output.resolve())
    source_raw = source.encode()
    # Close the validation/render TOCTOU window before publishing any output.
    manifest_after, payloads_after = validate_production_inputs(
        args.manifest, args.manifest_sha256, args.certificate_dir,
        args.include_root, args.payload_manifest, args.payload_manifest_sha256)
    if manifest_after != manifest or payloads_after != payloads:
        parser.error("pinned inputs changed during rendering")
    receipt = {"generator_sha256": generator_sha256,
        "generator_source": "research/problems/erdos-85-wip-01/sat49/generate_small_high_cube_lean_module.py",
        "certificate_dir": str(args.certificate_dir),
        "include_root": str(args.include_root), "jobs": 406,
        "module": str(args.output), "module_bytes": len(source_raw),
        "module_sha256": hashlib.sha256(source_raw).hexdigest(),
        "payload_identity_sha256": hashlib.sha256(canonical(payloads)).hexdigest(),
        "payload_manifest": str(args.payload_manifest),
        "payload_manifest_sha256": args.payload_manifest_sha256,
        "root_manifest": str(args.manifest),
        "root_manifest_sha256": args.manifest_sha256, "schema": MODULE_RECEIPT_SCHEMA,
        "source_module": SOURCE_MODULE}
    atomic_create(args.output, source_raw)
    # Receipt-last gate: the emitted module is intentionally left unreceipted
    # if any input, generator byte, or module byte drifts during publication.
    manifest_final, payloads_final = validate_production_inputs(
        args.manifest, args.manifest_sha256, args.certificate_dir,
        args.include_root, args.payload_manifest, args.payload_manifest_sha256)
    if (manifest_final != manifest or payloads_final != payloads
            or sha256(Path(__file__)) != generator_sha256
            or sha256(args.output) != receipt["module_sha256"]):
        raise ValueError("generator/input/module drift before receipt publication")
    atomic_create(receipt_path, canonical(receipt))
    print(f"WROTE {args.output} receipt={receipt_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
