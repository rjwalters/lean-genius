#!/usr/bin/env python3
"""Assemble direct H7 LRATs and checked binary-parent theorem overrides."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

from generate_h7_t0_cube_one_cover_lean import (
    LEFT, RIGHT, SCHEMA, cnf_expression, lean_stem, portable_include_paths,
    sha256,
)
from generate_h7_t0_cube_one_mixed_lean import (
    expected_parent_ids, manifest_sha256, render_check, validate_payloads,
)


OVERRIDE_SCHEMA = "erdos85-h7-binary-parent-overrides-v1"
LEAN_NAME = re.compile(
    r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*"
)


def load_and_validate(parent_path: Path, override_path: Path,
                      direct_ledger: Path, direct_dir: Path
                      ) -> tuple[dict, dict[str, dict[str, str]], dict[str, Path]]:
    parent = json.loads(parent_path.read_text())
    overrides = json.loads(override_path.read_text())
    if parent.get("schema") != SCHEMA:
        raise ValueError("unsupported parent manifest schema")
    if overrides.get("schema") != OVERRIDE_SCHEMA:
        raise ValueError("unsupported override manifest schema")
    if (overrides.get("parent_manifest_sha256") != manifest_sha256(parent_path) or
            overrides.get("base_sha256") != parent.get("base_sha256")):
        raise ValueError("override manifest does not bind parent/base")
    if parent.get("left") != LEFT or parent.get("right") != RIGHT:
        raise ValueError("parent selectors differ from checked Lean arrays")
    if (parent.get("variables"), parent.get("base_clauses")) != (30646, 1330469):
        raise ValueError("unexpected h7/t0 cube-one base shape")
    base = Path(parent.get("base", ""))
    if not base.is_file() or sha256(base) != parent.get("base_sha256"):
        raise ValueError("parent base CNF is missing or changed")
    jobs_list = parent.get("jobs")
    if not isinstance(jobs_list, list) or len(jobs_list) != 66:
        raise ValueError("parent manifest must contain 66 jobs")
    jobs = {job.get("id"): job for job in jobs_list}
    if None in jobs or set(jobs) != expected_parent_ids():
        raise ValueError("parent manifest does not contain the exact cover")
    for job_id, job in jobs.items():
        if job_id == "h7_t0_cube1.cover-left":
            expected_kind, expected_units = "cover-left", [-x for x in LEFT]
        elif job_id == "h7_t0_cube1.cover-right":
            expected_kind, expected_units = "cover-right", [-x for x in RIGHT]
        else:
            match = re.fullmatch(r"h7_t0_cube1\.cube-([0-7])-([0-7])", job_id)
            assert match is not None
            li, ri = map(int, match.groups())
            expected_kind, expected_units = "cube", [LEFT[li], RIGHT[ri]]
            if (job.get("left_index"), job.get("right_index")) != (li, ri):
                raise ValueError(f"parent cube index mismatch: {job_id}")
        if job.get("kind") != expected_kind or job.get("units") != expected_units:
            raise ValueError(f"parent job metadata mismatch: {job_id}")
    entries = overrides.get("parents")
    if not isinstance(entries, dict) or not entries:
        raise ValueError("override manifest must contain at least one binary parent")
    if not set(entries) < set(jobs):
        raise ValueError("binary overrides must be a strict subset of parent jobs")
    for parent_id, entry in entries.items():
        if jobs[parent_id].get("kind") != "cube":
            raise ValueError(f"binary override is not a cube parent: {parent_id}")
        if (not isinstance(entry, dict) or set(entry) != {"module", "theorem"} or
                any(not isinstance(value, str) or not LEAN_NAME.fullmatch(value)
                    for value in entry.values())):
            raise ValueError(f"invalid binary theorem override: {parent_id}")
    direct_ids = set(jobs) - set(entries)
    direct_jobs = {
        job_id: (job["units"], parent["base_clauses"] + len(job["units"]))
        for job_id, job in jobs.items() if job_id in direct_ids
    }
    payloads = validate_payloads(
        direct_ids, direct_ledger, direct_dir, direct_jobs, base,
        parent["variables"], parent["base_clauses"])
    return parent, entries, payloads


def render(parent: dict, overrides: dict[str, dict[str, str]],
           direct: dict[str, str]) -> str:
    modules = list(dict.fromkeys(entry["module"] for entry in overrides.values()))
    lines = [f"import {module}" for module in modules]
    lines.extend([
        "import Proofs.Erdos85OrderFortyNineSevenHighCertificates",
        "import Proofs.Erdos85OrderFortyNineLratCertificateBase", "",
        "/-! GENERATED direct/binary hybrid h7/t0 cube-one certificate bank. -/", "",
        "namespace Erdos85", "", "open Std Sat Std.Tactic.BVDecide", "",
    ])
    for job in parent["jobs"]:
        if job["id"] not in overrides:
            render_check(lines, job["id"], cnf_expression(job), direct[job["id"]])
    lines.extend([
        "theorem sevenHighT0CubeOneBinaryHybridGrid :",
        "    SevenHighT0CubeOneCheckedGrid := by",
        f"  refine ⟨{lean_stem('h7_t0_cube1.cover-left')}Unsat,",
        f"    {lean_stem('h7_t0_cube1.cover-right')}Unsat, ?_⟩",
        "  intro left right", "  fin_cases left <;> fin_cases right",
    ])
    jobs = {job["id"]: job for job in parent["jobs"]}
    for li in range(8):
        for ri in range(8):
            job_id = f"h7_t0_cube1.cube-{li}-{ri}"
            theorem = (overrides[job_id]["theorem"] if job_id in overrides
                       else f"{lean_stem(job_id)}Unsat")
            lines.append(f"  · exact {theorem}")
    lines.extend([
        "", "theorem sevenHighT0_canonicalExcluded_of_binaryHybridCertificates :",
        "    SevenHighCanonicalRepresentativeExcluded 0 0 :=",
        "  sevenHighT0_canonicalExcluded_of_cubeOne_checkedGrid",
        "    sevenHighT0CubeOneBinaryHybridGrid", "",
        "theorem orderFortyNineStratumExcluded_seven_of_binaryHybridCertificates :",
        "    OrderFortyNineStratumExcluded 7 :=",
        "  orderFortyNineStratumExcluded_seven_of_t0",
        "    sevenHighT0_canonicalExcluded_of_binaryHybridCertificates", "",
        "end Erdos85", "",
    ])
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--parent-manifest", type=Path, required=True)
    parser.add_argument("--override-manifest", type=Path, required=True)
    parser.add_argument("--direct-ledger", type=Path, required=True)
    parser.add_argument("--direct-certificate-dir", type=Path, required=True)
    parser.add_argument("--include-root", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    parent, overrides, direct = load_and_validate(
        args.parent_manifest.resolve(), args.override_manifest.resolve(),
        args.direct_ledger.resolve(), args.direct_certificate_dir.resolve())
    portable = portable_include_paths(
        direct, args.include_root.resolve(), args.output.resolve())
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(render(parent, overrides, portable))
    print(f"WROTE {args.output.resolve()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
