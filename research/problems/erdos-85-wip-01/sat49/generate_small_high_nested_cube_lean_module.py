#!/usr/bin/env python3
"""Assemble mixed direct/nested h3/h5 LRAT grids into one Lean module."""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path

from generate_small_high_cube_jobs import jobs_for, sha256
from generate_small_high_cube_lean_module import (
    CELL_LEAN,
    cnf_expression,
    lean_stem,
    payload_path,
)
from generate_small_high_nested_cube_jobs import SELECTORS, nested_jobs
from generate_small_high_third_cube_jobs import LEFT as THIRD_LEFT
from generate_small_high_third_cube_jobs import RIGHT as THIRD_RIGHT
from generate_small_high_third_cube_jobs import third_jobs


def load_and_validate(parent_path: Path, nested_path: Path,
                      certificate_dir: Path, third_path: Path | None = None
                      ) -> tuple[dict, dict, dict | None]:
    parent = json.loads(parent_path.read_text())
    nested = json.loads(nested_path.read_text())
    if parent.get("schema") != "erdos85-small-high-cube-jobs-v1":
        raise ValueError("unsupported parent manifest schema")
    if nested.get("schema") != "erdos85-small-high-nested-cube-jobs-v1":
        raise ValueError("unsupported nested manifest schema")
    if nested.get("parent_manifest_sha256") != sha256(parent_path):
        raise ValueError("nested manifest does not bind the supplied parent manifest")
    cells = parent.get("cells")
    leaves = nested.get("leaves")
    if not isinstance(cells, dict) or set(cells) != set(CELL_LEAN):
        raise ValueError("parent manifest must contain exactly seven cells")
    if not isinstance(leaves, dict) or not leaves:
        raise ValueError("nested manifest must contain at least one hard parent leaf")
    third = json.loads(third_path.read_text()) if third_path is not None else None
    third_leaves = set()
    if third is not None:
        if third.get("schema") != "erdos85-small-high-third-cube-jobs-v1":
            raise ValueError("unsupported third manifest schema")
        if third.get("parent_manifest_sha256") != sha256(nested_path):
            raise ValueError("third manifest does not bind the supplied nested manifest")
        if not isinstance(third.get("leaves"), dict) or not third["leaves"]:
            raise ValueError("third manifest must contain at least one hard nested leaf")
        third_leaves = set(third["leaves"])
    parent_lookup = {}
    seen = set()
    for cell_name, cell in cells.items():
        jobs = cell.get("jobs")
        if jobs != jobs_for(cell_name):
            raise ValueError(f"{cell_name}: malformed or incomplete parent grid")
        for job in jobs:
            job_id = job.get("id")
            if not isinstance(job_id, str) or job_id in parent_lookup:
                raise ValueError(f"invalid or duplicate parent job: {job_id}")
            parent_lookup[job_id] = (cell_name, job)
    for parent_id, leaf in leaves.items():
        if parent_id not in parent_lookup:
            raise ValueError(f"nested leaf has unknown parent: {parent_id}")
        cell_name, parent_job = parent_lookup[parent_id]
        if parent_job.get("kind") != "cube" or leaf.get("cell") != cell_name:
            raise ValueError(f"nested leaf/parent mismatch: {parent_id}")
        parent_cell = cells[cell_name]
        inherited = ("base", "base_sha256", "variables", "base_clauses")
        if (leaf.get("parent_units") != parent_job.get("units") or
                any(leaf.get(key) != parent_cell.get(key) for key in inherited)):
            raise ValueError(f"nested leaf metadata mismatch: {parent_id}")
        expected_left, expected_right = SELECTORS[cell_name]
        if (leaf.get("left") != list(expected_left) or
                leaf.get("right") != list(expected_right)):
            raise ValueError(f"nested selector mismatch: {parent_id}")
        jobs = leaf.get("jobs")
        if jobs != nested_jobs(parent_id, expected_left, expected_right):
            raise ValueError(f"{parent_id}: malformed or incomplete nested grid")
        for job in jobs:
            job_id = job.get("id")
            if not isinstance(job_id, str) or job_id in seen:
                raise ValueError(f"duplicate or invalid nested job id: {job_id}")
            seen.add(job_id)
            if job_id not in third_leaves:
                payload_path(certificate_dir, job_id)
    hard = set(leaves)
    for job_id in parent_lookup:
        if job_id not in hard:
            payload_path(certificate_dir, job_id)
    if third is not None:
        nested_lookup = {
            job["id"]: (leaf, job)
            for leaf in leaves.values() for job in leaf["jobs"]
            if job.get("kind") == "cube"
        }
        third_seen = set()
        for nested_id, leaf in third["leaves"].items():
            if nested_id not in nested_lookup:
                raise ValueError(f"third leaf has unknown nested parent: {nested_id}")
            parent_leaf, parent_job = nested_lookup[nested_id]
            if (leaf.get("cell") != parent_leaf.get("cell") or
                    leaf.get("parent_units") != [
                        *parent_leaf["parent_units"], *parent_job["units"]]):
                raise ValueError(f"third leaf/parent mismatch: {nested_id}")
            if (leaf.get("left") != list(THIRD_LEFT) or
                    leaf.get("right") != list(THIRD_RIGHT)):
                raise ValueError(f"third selector mismatch: {nested_id}")
            jobs = leaf.get("jobs")
            if jobs != third_jobs(nested_id):
                raise ValueError(f"{nested_id}: malformed or incomplete third grid")
            for job in jobs:
                job_id = job.get("id")
                if not isinstance(job_id, str) or job_id in third_seen:
                    raise ValueError(f"duplicate or invalid third job id: {job_id}")
                third_seen.add(job_id)
                payload_path(certificate_dir, job_id)
    return parent, nested, third


def nested_arrays(cell_name: str) -> tuple[str, str]:
    _, masks, family = CELL_LEAN[cell_name]
    title = family.title()
    return (f"orderFortyNine{title}HighNestedCubeLeftVariables {masks}",
            f"orderFortyNine{title}HighNestedCubeRightVariables {masks}")


def nested_cnf_expression(cell_name: str, parent_job: dict,
                          child_job: dict) -> str:
    base = cnf_expression(cell_name, parent_job)
    left, right = nested_arrays(cell_name)
    kind = child_job["kind"]
    if kind == "cover-left":
        return f"orderFortyNineSmallHighLeftCoverCnf ({base}) ({left})"
    if kind == "cover-right":
        return f"orderFortyNineSmallHighRightCoverCnf ({base}) ({right})"
    li, ri = child_job["left_index"], child_job["right_index"]
    return ("orderFortyNineSmallHighPositiveCubeCnf "
            f"({base}) ({left})[{li}] ({right})[{ri}]")


def third_cnf_expression(cell_name: str, parent_job: dict,
                         nested_job: dict, child_job: dict) -> str:
    base = nested_cnf_expression(cell_name, parent_job, nested_job)
    left = "orderFortyNineThreeHighHardThirdCubeLeftVariables"
    right = "orderFortyNineThreeHighHardThirdCubeRightVariables"
    kind = child_job["kind"]
    if kind == "cover-left":
        return f"orderFortyNineSmallHighLeftCoverCnf ({base}) ({left})"
    if kind == "cover-right":
        return f"orderFortyNineSmallHighRightCoverCnf ({base}) ({right})"
    li, ri = child_job["left_index"], child_job["right_index"]
    return ("orderFortyNineSmallHighPositiveCubeCnf "
            f"({base}) ({left})[{li}] ({right})[{ri}]")


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


def render_check(lines: list[str], stem: str, cnf: str, payload: str) -> None:
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


def render(parent: dict, nested: dict, certificate_dir: Path,
           include_root: Path, output: Path, third: dict | None = None) -> str:
    lines = [
        "import Proofs.Erdos85OrderFortyNineSmallHighCubeGridTerminal",
        "import Proofs.Erdos85OrderFortyNineSmallHighNestedCubeSelectors",
        "import Proofs.Erdos85OrderFortyNineSmallHighThirdCubeSelectors",
        "import Proofs.Erdos85OrderFortyNineLratCertificateBase", "",
        "/-! Generated checked direct and nested small-high cube grids. -/", "",
        "namespace Erdos85", "", "open Std Sat Std.Tactic.BVDecide", "",
    ]
    hard = set(nested["leaves"])
    third_leaves = set(third["leaves"]) if third is not None else set()
    parent_lookup = {}
    for cell_name in CELL_LEAN:
        for job in parent["cells"][cell_name]["jobs"]:
            parent_lookup[job["id"]] = (cell_name, job)
            if job["id"] not in hard:
                payload = portable_include_path(
                    payload_path(certificate_dir, job["id"]),
                    include_root, output)
                render_check(lines, lean_stem(job["id"]),
                             cnf_expression(cell_name, job),
                             payload)
    for parent_id, leaf in nested["leaves"].items():
        cell_name, parent_job = parent_lookup[parent_id]
        for child in leaf["jobs"]:
            if child["id"] in third_leaves:
                continue
            payload = portable_include_path(
                payload_path(certificate_dir, child["id"]),
                include_root, output)
            render_check(lines, lean_stem(child["id"]),
                         nested_cnf_expression(cell_name, parent_job, child),
                         payload)
        if third is not None:
            nested_lookup = {job["id"]: job for job in leaf["jobs"]}
            for nested_id in sorted(set(third["leaves"]) & set(nested_lookup)):
                nested_job = nested_lookup[nested_id]
                third_leaf = third["leaves"][nested_id]
                for child in third_leaf["jobs"]:
                    payload = portable_include_path(
                        payload_path(certificate_dir, child["id"]),
                        include_root, output)
                    render_check(
                        lines, lean_stem(child["id"]),
                        third_cnf_expression(cell_name, parent_job,
                                             nested_job, child), payload)
                base = nested_cnf_expression(cell_name, parent_job, nested_job)
                left = "orderFortyNineThreeHighHardThirdCubeLeftVariables"
                right = "orderFortyNineThreeHighHardThirdCubeRightVariables"
                grid_stem = lean_stem(f"{nested_id}.third-grid")
                lines.extend([
                    f"theorem {grid_stem} :",
                    "    OrderFortyNineSmallHighCheckedCubeGrid",
                    f"      ({base}) ({left}) ({right}) := by",
                    "  refine ⟨?_, ?_, ?_⟩",
                    f"  · exact {lean_stem(nested_id + '.third.cover-left')}_unsat",
                    f"  · exact {lean_stem(nested_id + '.third.cover-right')}_unsat",
                    "  · intro li ri",
                    "    fin_cases li <;> fin_cases ri",
                ])
                for li in range(8):
                    for ri in range(8):
                        child_id = f"{nested_id}.third.cube-{li}-{ri}"
                        lines.append(f"    · exact {lean_stem(child_id)}_unsat")
                lines.extend([
                    "",
                    f"theorem {lean_stem(nested_id)}_unsat : ({base}).Unsat :=",
                    f"  orderFortyNineSmallHigh_unsat_of_checkedCubeGrid {grid_stem}",
                    "",
                ])
        left, right = nested_arrays(cell_name)
        parent_cnf = cnf_expression(cell_name, parent_job)
        grid_stem = lean_stem(f"{parent_id}.nested-grid")
        left_stem = lean_stem(f"{parent_id}.nested.cover-left")
        right_stem = lean_stem(f"{parent_id}.nested.cover-right")
        lines.extend([
            f"theorem {grid_stem} :",
            "    OrderFortyNineSmallHighCheckedCubeGrid",
            f"      ({parent_cnf}) ({left}) ({right}) := by",
            "  refine ⟨?_, ?_, ?_⟩",
            f"  · exact {left_stem}_unsat",
            f"  · exact {right_stem}_unsat",
            "  · intro li ri",
            "    fin_cases li <;> fin_cases ri",
        ])
        for li in range(len(leaf["left"])):
            for ri in range(len(leaf["right"])):
                child_id = f"{parent_id}.nested.cube-{li}-{ri}"
                lines.append(f"    · exact {lean_stem(child_id)}_unsat")
        parent_stem = lean_stem(parent_id)
        lines.extend([
            "",
            f"theorem {parent_stem}_unsat : ({parent_cnf}).Unsat :=",
            f"  orderFortyNineSmallHigh_unsat_of_checkedCubeGrid {grid_stem}", "",
        ])
    for cell_name, (base, masks, family) in CELL_LEAN.items():
        title = family.title()
        left = f"orderFortyNine{title}HighCubeLeftVariables {masks}"
        right = f"orderFortyNine{title}HighCubeRightVariables {masks}"
        cell_stem = lean_stem(cell_name)
        lines.extend([
            f"theorem {cell_stem}Grid :",
            f"    OrderFortyNineSmallHighCheckedCubeGrid ({base}) ({left}) ({right}) := by",
            "  refine ⟨?_, ?_, ?_⟩",
            f"  · exact {lean_stem(f'{cell_name}.cover-left')}_unsat",
            f"  · exact {lean_stem(f'{cell_name}.cover-right')}_unsat",
            "  · intro li ri",
            "    fin_cases li <;> fin_cases ri",
        ])
        for li in range(7):
            for ri in range(8):
                lines.append(
                    f"    · exact {lean_stem(f'{cell_name}.cube-{li}-{ri}')}_unsat"
                )
        lines.extend([
            "",
            f"theorem {cell_stem}Base_unsat : ({base}).Unsat :=",
            f"  orderFortyNineSmallHigh_unsat_of_checkedCubeGrid {cell_stem}Grid", "",
        ])
    lines.extend([
        "theorem orderFortyNineStratumExcluded_three_of_mixedCubeCertificates :",
        "    OrderFortyNineStratumExcluded 3 :=",
        "  orderFortyNineStratumExcluded_three_of_cubeBaseUnsat",
        "    smallHighH3B1Base_unsat smallHighH3C1Base_unsat",
        "    smallHighH3C2Base_unsat smallHighH3Dist2Base_unsat", "",
        "theorem orderFortyNineStratumExcluded_five_of_mixedCubeCertificates :",
        "    OrderFortyNineStratumExcluded 5 :=",
        "  orderFortyNineStratumExcluded_five_of_cubeBaseUnsat",
        "    smallHighH5T0Base_unsat smallHighH5T1Base_unsat",
        "    smallHighH5T2Base_unsat", "",
    ])
    lines.extend(["end Erdos85", ""])
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--parent-manifest", type=Path, required=True)
    parser.add_argument("--nested-manifest", type=Path, required=True)
    parser.add_argument("--third-manifest", type=Path)
    parser.add_argument("--certificate-dir", type=Path, required=True)
    parser.add_argument(
        "--include-root", type=Path, required=True,
        help="portable certificate root that must contain every LRAT payload")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    parent, nested, third = load_and_validate(
        args.parent_manifest.resolve(), args.nested_manifest.resolve(),
        args.certificate_dir.resolve(),
        args.third_manifest.resolve() if args.third_manifest else None)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(render(
        parent, nested, args.certificate_dir.resolve(),
        args.include_root.resolve(), args.output.resolve(), third))
    print(f"WROTE {args.output.resolve()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
