#!/usr/bin/env python3
"""Assemble mixed direct/nested h3/h5 LRAT grids into one Lean module."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from generate_small_high_cube_jobs import sha256
from generate_small_high_cube_lean_module import (
    CELL_LEAN,
    cnf_expression,
    lean_stem,
    payload_path,
)
from generate_small_high_nested_cube_jobs import SELECTORS


def load_and_validate(parent_path: Path, nested_path: Path,
                      certificate_dir: Path) -> tuple[dict, dict]:
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
    parent_lookup = {}
    seen = set()
    for cell_name, cell in cells.items():
        jobs = cell.get("jobs")
        if not isinstance(jobs, list) or len(jobs) != 58:
            raise ValueError(f"{cell_name}: expected 58 parent jobs")
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
        expected_left, expected_right = SELECTORS[cell_name]
        if (leaf.get("left") != list(expected_left) or
                leaf.get("right") != list(expected_right)):
            raise ValueError(f"nested selector mismatch: {parent_id}")
        jobs = leaf.get("jobs")
        expected_count = 2 + len(expected_left) * len(expected_right)
        if not isinstance(jobs, list) or len(jobs) != expected_count:
            raise ValueError(f"{parent_id}: expected {expected_count} nested jobs")
        kinds = [job.get("kind") for job in jobs]
        if kinds.count("cover-left") != 1 or kinds.count("cover-right") != 1:
            raise ValueError(f"{parent_id}: malformed nested covers")
        cubes = {(job.get("left_index"), job.get("right_index"))
                 for job in jobs if job.get("kind") == "cube"}
        expected_cubes = {(li, ri) for li in range(len(expected_left))
                          for ri in range(len(expected_right))}
        if cubes != expected_cubes:
            raise ValueError(f"{parent_id}: incomplete nested grid")
        for job in jobs:
            job_id = job.get("id")
            if not isinstance(job_id, str) or job_id in seen:
                raise ValueError(f"duplicate or invalid nested job id: {job_id}")
            seen.add(job_id)
            payload_path(certificate_dir, job_id)
    hard = set(leaves)
    for job_id in parent_lookup:
        if job_id not in hard:
            payload_path(certificate_dir, job_id)
    return parent, nested


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


def render_check(lines: list[str], stem: str, cnf: str, payload: Path) -> None:
    lines.extend([
        f"def {stem}Proof : Array LRAT.IntAction :=",
        "  parseOrderFortyNineLratProof",
        f"    (include_str \"{payload}\")", "",
        "set_option maxHeartbeats 0 in",
        "set_option maxRecDepth 1000000 in",
        f"theorem {stem}_check : LRAT.check {stem}Proof ({cnf}) := by",
        "  native_decide", "",
        f"theorem {stem}_unsat : ({cnf}).Unsat :=",
        f"  LRAT.check_sound _ _ {stem}_check", "",
    ])


def render(parent: dict, nested: dict, certificate_dir: Path) -> str:
    lines = [
        "import Proofs.Erdos85OrderFortyNineSmallHighCubeGridTerminal",
        "import Proofs.Erdos85OrderFortyNineSmallHighNestedCubeSelectors",
        "import Proofs.Erdos85OrderFortyNineLratCertificateBase", "",
        "/-! Generated checked direct and nested small-high cube grids. -/", "",
        "namespace Erdos85", "", "open Std Sat Std.Tactic.BVDecide", "",
    ]
    hard = set(nested["leaves"])
    parent_lookup = {}
    for cell_name in CELL_LEAN:
        for job in parent["cells"][cell_name]["jobs"]:
            parent_lookup[job["id"]] = (cell_name, job)
            if job["id"] not in hard:
                render_check(lines, lean_stem(job["id"]),
                             cnf_expression(cell_name, job),
                             payload_path(certificate_dir, job["id"]))
    for parent_id, leaf in nested["leaves"].items():
        cell_name, parent_job = parent_lookup[parent_id]
        for child in leaf["jobs"]:
            render_check(lines, lean_stem(child["id"]),
                         nested_cnf_expression(cell_name, parent_job, child),
                         payload_path(certificate_dir, child["id"]))
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
    lines.extend(["end Erdos85", ""])
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--parent-manifest", type=Path, required=True)
    parser.add_argument("--nested-manifest", type=Path, required=True)
    parser.add_argument("--certificate-dir", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    parent, nested = load_and_validate(
        args.parent_manifest.resolve(), args.nested_manifest.resolve(),
        args.certificate_dir.resolve())
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(render(parent, nested, args.certificate_dir.resolve()))
    print(f"WROTE {args.output.resolve()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
