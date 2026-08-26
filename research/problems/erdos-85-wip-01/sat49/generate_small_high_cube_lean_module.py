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
import json
import os
import re
from pathlib import Path


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
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--certificate-dir", type=Path, required=True)
    parser.add_argument(
        "--include-root", type=Path, required=True,
        help="portable certificate root that must contain every LRAT payload")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    manifest = load_and_validate(args.manifest, args.certificate_dir)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(render(
        manifest, args.certificate_dir.resolve(), args.include_root.resolve(),
        args.output.resolve()))
    print(f"WROTE {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
