#!/usr/bin/env python3
"""Assemble direct and nested h7/t0 cube-one LRATs into checked Lean."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path

from generate_h7_t0_cube_one_cover_lean import (
    LEFT as PARENT_LEFT,
    RIGHT as PARENT_RIGHT,
    SCHEMA as PARENT_SCHEMA,
    cnf_expression as parent_cnf_expression,
    lean_stem,
    materialized_identity,
    payload_path,
    portable_include_paths,
    read_accepted_ledger,
    sha256,
)
from generate_h7_t0_cube_one_nested_jobs import LEFT, RIGHT


NESTED_SCHEMA = "erdos85-h7-t0-cube1-nested-jobs-v1"


def manifest_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def expected_parent_ids() -> set[str]:
    return {
        "h7_t0_cube1.cover-left",
        "h7_t0_cube1.cover-right",
        *(f"h7_t0_cube1.cube-{li}-{ri}"
          for li in range(8) for ri in range(8)),
    }


def validate_payloads(expected: set[str], ledger_path: Path,
                      certificate_dir: Path, jobs: dict[str, tuple[list[int], int]],
                      base: Path, variables: int, clauses: int) -> dict[str, Path]:
    accepted = read_accepted_ledger(ledger_path)
    missing, unexpected = expected - set(accepted), set(accepted) - expected
    if missing or unexpected:
        raise ValueError(
            f"{ledger_path}: coverage mismatch: missing={sorted(missing)}, "
            f"unexpected={sorted(unexpected)}")
    payloads: dict[str, Path] = {}
    for job_id in sorted(expected):
        units, expected_clauses = jobs[job_id]
        if expected_clauses != clauses + len(units):
            raise ValueError(f"clause-count mismatch for {job_id}")
        cnf_hash, cnf_bytes = materialized_identity(
            base, variables, clauses, units)
        metadata = accepted[job_id]
        if (metadata.get("emitted_cnf_sha256") != cnf_hash or
                metadata.get("solved_cnf_sha256") != cnf_hash or
                int(metadata.get("cnf_bytes", -1)) != cnf_bytes or
                int(metadata.get("maxvar", -1)) != variables):
            raise ValueError(f"materialized CNF identity mismatch for {job_id}")
        payload = payload_path(certificate_dir, job_id)
        if payload.stat().st_size != int(metadata["lrat_bytes"]):
            raise ValueError(f"LRAT size mismatch for {job_id}")
        if sha256(payload) != metadata["lrat_sha256"]:
            raise ValueError(f"LRAT hash mismatch for {job_id}")
        payloads[job_id] = payload
    return payloads


def load_and_validate(parent_path: Path, nested_path: Path,
                      direct_ledger: Path, nested_ledger: Path,
                      direct_dir: Path, nested_dir: Path
                      ) -> tuple[dict, dict, dict[str, Path], dict[str, Path]]:
    parent = json.loads(parent_path.read_text())
    nested = json.loads(nested_path.read_text())
    if parent.get("schema") != PARENT_SCHEMA:
        raise ValueError("unsupported parent manifest schema")
    if nested.get("schema") != NESTED_SCHEMA:
        raise ValueError("unsupported nested manifest schema")
    if nested.get("parent_manifest_sha256") != manifest_sha256(parent_path):
        raise ValueError("nested manifest does not bind the supplied parent manifest")
    if parent.get("left") != PARENT_LEFT or parent.get("right") != PARENT_RIGHT:
        raise ValueError("parent selectors differ from the checked Lean arrays")
    if nested.get("base_sha256") != parent.get("base_sha256"):
        raise ValueError("nested and parent manifests bind different base CNFs")
    base = Path(parent.get("base", ""))
    if not base.is_file() or sha256(base) != parent.get("base_sha256"):
        raise ValueError("base CNF is missing or differs from the manifest hash")
    variables, clauses = parent.get("variables"), parent.get("base_clauses")
    if (variables, clauses) != (30646, 1330469):
        raise ValueError("unexpected h7/t0 cube-one base CNF shape")
    if (nested.get("variables"), nested.get("base_clauses")) != (variables, clauses):
        raise ValueError("nested manifest has a different base CNF shape")

    parent_jobs_list = parent.get("jobs")
    if not isinstance(parent_jobs_list, list) or len(parent_jobs_list) != 66:
        raise ValueError("parent manifest must contain exactly 66 jobs")
    parent_jobs = {job.get("id"): job for job in parent_jobs_list}
    if None in parent_jobs or len(parent_jobs) != 66 or set(parent_jobs) != expected_parent_ids():
        raise ValueError("parent manifest does not contain the exact checked cover")
    for job_id, job in parent_jobs.items():
        if job_id == "h7_t0_cube1.cover-left":
            expected_kind, expected_units = "cover-left", [-x for x in PARENT_LEFT]
        elif job_id == "h7_t0_cube1.cover-right":
            expected_kind, expected_units = "cover-right", [-x for x in PARENT_RIGHT]
        else:
            match = re.fullmatch(r"h7_t0_cube1\.cube-([0-7])-([0-7])", job_id)
            if match is None:
                raise ValueError(f"malformed parent job id: {job_id}")
            li, ri = map(int, match.groups())
            expected_kind = "cube"
            expected_units = [PARENT_LEFT[li], PARENT_RIGHT[ri]]
            if (job.get("left_index"), job.get("right_index")) != (li, ri):
                raise ValueError(f"parent cube index mismatch: {job_id}")
        if job.get("kind") != expected_kind or job.get("units") != expected_units:
            raise ValueError(f"parent job metadata mismatch: {job_id}")
    leaves = nested.get("leaves")
    if not isinstance(leaves, dict) or not leaves:
        raise ValueError("nested manifest must contain at least one hard parent")
    hard = set(leaves)
    if not hard <= set(parent_jobs):
        raise ValueError("nested manifest contains an unknown hard parent")

    nested_jobs: dict[str, tuple[list[int], int]] = {}
    for parent_id, leaf in leaves.items():
        parent_job = parent_jobs[parent_id]
        if parent_job.get("kind") != "cube":
            raise ValueError(f"nested parent is not a positive cube: {parent_id}")
        if (leaf.get("parent_left_index") != parent_job.get("left_index") or
                leaf.get("parent_right_index") != parent_job.get("right_index") or
                leaf.get("parent_units") != parent_job.get("units") or
                leaf.get("left") != list(LEFT) or leaf.get("right") != list(RIGHT)):
            raise ValueError(f"nested parent metadata mismatch: {parent_id}")
        children = leaf.get("jobs")
        if not isinstance(children, list) or len(children) != 66:
            raise ValueError(f"{parent_id}: expected exactly 66 nested jobs")
        child_ids: set[str] = set()
        cubes: set[tuple[int, int]] = set()
        covers: set[str] = set()
        for child in children:
            child_id, kind = child.get("id"), child.get("kind")
            if not isinstance(child_id, str) or child_id in nested_jobs:
                raise ValueError(f"invalid or duplicate nested job id: {child_id}")
            child_ids.add(child_id)
            if kind == "cover-left":
                covers.add(kind)
                expected_units = [-literal for literal in LEFT]
            elif kind == "cover-right":
                covers.add(kind)
                expected_units = [-literal for literal in RIGHT]
            elif kind == "cube":
                li, ri = child.get("left_index"), child.get("right_index")
                if not isinstance(li, int) or not isinstance(ri, int) or not (0 <= li < 8 and 0 <= ri < 8):
                    raise ValueError(f"invalid nested cube indices: {child_id}")
                cubes.add((li, ri))
                expected_units = [LEFT[li], RIGHT[ri]]
            else:
                raise ValueError(f"invalid nested job kind: {child_id}")
            if child_id != (f"{parent_id}.nested.{kind}" if kind.startswith("cover-")
                            else f"{parent_id}.nested.cube-{li}-{ri}"):
                raise ValueError(f"noncanonical nested job id: {child_id}")
            if child.get("units") != expected_units:
                raise ValueError(f"nested units mismatch: {child_id}")
            all_units = [*parent_job["units"], *expected_units]
            nested_jobs[child_id] = (all_units, clauses + len(all_units))
        if covers != {"cover-left", "cover-right"} or cubes != {
                (li, ri) for li in range(8) for ri in range(8)}:
            raise ValueError(f"incomplete nested cover: {parent_id}")

    direct_expected = set(parent_jobs) - hard
    direct_jobs = {
        job_id: (job["units"], clauses + len(job["units"]))
        for job_id, job in parent_jobs.items() if job_id in direct_expected
    }
    direct_payloads = validate_payloads(
        direct_expected, direct_ledger, direct_dir, direct_jobs,
        base, variables, clauses)
    nested_payloads = validate_payloads(
        set(nested_jobs), nested_ledger, nested_dir, nested_jobs,
        base, variables, clauses)
    return parent, nested, direct_payloads, nested_payloads


def nested_cnf_expression(parent_job: dict, child: dict) -> str:
    pl, pr = parent_job["left_index"], parent_job["right_index"]
    parent_left = f"sevenHighT0CubeOneLeftVariables[{pl}]"
    parent_right = f"sevenHighT0CubeOneRightVariables[{pr}]"
    kind = child["kind"]
    if kind == "cover-left":
        return f"sevenHighT0CubeOneNestedLeftCoverCnf {parent_left} {parent_right}"
    if kind == "cover-right":
        return f"sevenHighT0CubeOneNestedRightCoverCnf {parent_left} {parent_right}"
    li, ri = child["left_index"], child["right_index"]
    return (f"sevenHighT0CubeOneNestedPositiveCnf {parent_left} {parent_right} "
            f"sevenHighT0CubeOneNestedLeftVariables[{li}] "
            f"sevenHighT0CubeOneNestedRightVariables[{ri}]")


def render_check(lines: list[str], job_id: str, cnf: str, payload: str) -> None:
    stem = lean_stem(job_id)
    lines.extend([
        f"private def {stem}Proof : Array LRAT.IntAction :=",
        "  parseOrderFortyNineLratProof",
        f"    (include_str {json.dumps(payload)})", "",
        "set_option maxHeartbeats 0 in",
        "set_option maxRecDepth 1000000 in",
        f"private theorem {stem}Check : LRAT.check {stem}Proof ({cnf}) := by",
        "  native_decide", "",
        f"private theorem {stem}Unsat : ({cnf}).Unsat :=",
        f"  LRAT.check_sound _ _ {stem}Check", "",
    ])


def render(parent: dict, nested: dict, direct: dict[str, str],
           nested_payloads: dict[str, str]) -> str:
    lines = [
        "import Proofs.Erdos85OrderFortyNineSevenHighT0CubeOneNestedCover",
        "import Proofs.Erdos85OrderFortyNineLratCertificateBase", "",
        "/-! GENERATED mixed direct/nested certificates for the h7/t0 cube-one cover. -/",
        "", "namespace Erdos85", "", "open Std Sat Std.Tactic.BVDecide", "",
    ]
    jobs = {job["id"]: job for job in parent["jobs"]}
    hard = set(nested["leaves"])
    for job in parent["jobs"]:
        if job["id"] not in hard:
            render_check(lines, job["id"], parent_cnf_expression(job), direct[job["id"]])
    for parent_id, leaf in nested["leaves"].items():
        parent_job = jobs[parent_id]
        for child in leaf["jobs"]:
            render_check(lines, child["id"], nested_cnf_expression(parent_job, child),
                         nested_payloads[child["id"]])
        pl, pr = parent_job["left_index"], parent_job["right_index"]
        parent_left = f"sevenHighT0CubeOneLeftVariables[{pl}]"
        parent_right = f"sevenHighT0CubeOneRightVariables[{pr}]"
        grid = lean_stem(f"{parent_id}.nested-grid")
        lines.extend([
            f"private theorem {grid} :",
            f"    SevenHighT0CubeOneNestedCheckedGrid {parent_left} {parent_right} := by",
            "  refine ⟨?_, ?_, ?_⟩",
            f"  · exact {lean_stem(parent_id + '.nested.cover-left')}Unsat",
            f"  · exact {lean_stem(parent_id + '.nested.cover-right')}Unsat",
            "  · intro li ri", "    fin_cases li <;> fin_cases ri",
        ])
        for li in range(8):
            for ri in range(8):
                lines.append(f"    · exact {lean_stem(parent_id + f'.nested.cube-{li}-{ri}')}Unsat")
        lines.extend([
            "",
            f"private theorem {lean_stem(parent_id)}Unsat :",
            f"    ({parent_cnf_expression(parent_job)}).Unsat :=",
            f"  sevenHighT0CubeOne_parent_unsat_of_nestedCheckedGrid {grid}", "",
        ])
    lines.extend([
        "theorem sevenHighT0CubeOneMixedCertificateGrid :",
        "    SevenHighT0CubeOneCheckedGrid := by",
        f"  refine ⟨{lean_stem('h7_t0_cube1.cover-left')}Unsat,",
        f"    {lean_stem('h7_t0_cube1.cover-right')}Unsat, ?_⟩",
        "  intro left right", "  fin_cases left <;> fin_cases right",
    ])
    for li in range(8):
        for ri in range(8):
            lines.append(f"  · exact {lean_stem(f'h7_t0_cube1.cube-{li}-{ri}')}Unsat")
    lines.extend([
        "", "/-- Checked exclusion using direct certificates and nested hard-leaf grids. -/",
        "theorem sevenHighT0_canonicalExcluded_of_mixedCubeOne_certificates :",
        "    SevenHighCanonicalRepresentativeExcluded 0 0 :=",
        "  sevenHighT0_canonicalExcluded_of_cubeOne_checkedGrid",
        "    sevenHighT0CubeOneMixedCertificateGrid", "", "end Erdos85", "",
        "#print axioms Erdos85.sevenHighT0_canonicalExcluded_of_mixedCubeOne_certificates", "",
    ])
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--parent-manifest", type=Path, required=True)
    parser.add_argument("--nested-manifest", type=Path, required=True)
    parser.add_argument("--direct-ledger", type=Path, required=True)
    parser.add_argument("--nested-ledger", type=Path, required=True)
    parser.add_argument("--direct-certificate-dir", type=Path, required=True)
    parser.add_argument("--nested-certificate-dir", type=Path, required=True)
    parser.add_argument(
        "--include-root", type=Path, required=True,
        help="portable certificate root that must contain all direct and nested LRATs")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    parent, nested, direct, nested_payloads = load_and_validate(
        args.parent_manifest.resolve(), args.nested_manifest.resolve(),
        args.direct_ledger.resolve(), args.nested_ledger.resolve(),
        args.direct_certificate_dir.resolve(), args.nested_certificate_dir.resolve())
    args.output.parent.mkdir(parents=True, exist_ok=True)
    direct_includes = portable_include_paths(direct, args.include_root, args.output)
    nested_includes = portable_include_paths(
        nested_payloads, args.include_root, args.output)
    args.output.write_text(render(parent, nested, direct_includes, nested_includes))
    print(f"WROTE {args.output.resolve()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
