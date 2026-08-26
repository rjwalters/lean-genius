#!/usr/bin/env python3
"""Emit a checked Lean proof for one H7 binary-tree parent."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from generate_h7_binary_tree_jobs import validate_bound_manifest
from generate_h7_t0_cube_one_cover_lean import (
    cnf_expression as parent_cnf_expression,
    lean_stem,
    portable_include_paths,
)
from generate_h7_t0_cube_one_mixed_lean import validate_payloads, render_check


def branch_cnf(base: str, variables: list[int], bits: list[bool]) -> str:
    result = base
    for variable, bit in zip(variables, bits, strict=True):
        value = "true" if bit else "false"
        result = f"cnfWithSignedUnit ({result}) {variable - 1} {value}"
    return result


def load_and_validate(manifest_path: Path, ledger: Path,
                      certificate_dir: Path) -> tuple[dict, dict, dict[str, Path]]:
    manifest = json.loads(manifest_path.read_text())
    base, leaves = validate_bound_manifest(manifest)
    parent = json.loads(Path(manifest["parent_manifest"]).read_text())
    matches = [job for job in parent["jobs"]
               if job.get("id") == manifest["parent_id"]]
    if len(matches) != 1:
        raise ValueError("binary parent is absent or duplicated")
    parent_job = matches[0]
    jobs = {
        leaf["id"]: (
            [*manifest["parent_units"], *leaf["path_units"]],
            manifest["base_clauses"] + len(manifest["parent_units"]) +
            len(leaf["path_units"]),
        )
        for leaf in leaves
    }
    payloads = validate_payloads(
        set(jobs), ledger, certificate_dir, jobs, base,
        manifest["variables"], manifest["base_clauses"])
    return manifest, parent_job, payloads


def tree_expression(parent_id: str, variables: list[int], depth: int = 0,
                    bits: tuple[bool, ...] = ()) -> str:
    if depth == len(variables):
        suffix = "".join("1" if bit else "0" for bit in bits)
        return f"(.leaf {lean_stem(parent_id + '.binary.leaf-' + suffix)}Unsat)"
    variable = variables[depth] - 1
    left = tree_expression(parent_id, variables, depth + 1, bits + (False,))
    right = tree_expression(parent_id, variables, depth + 1, bits + (True,))
    return f"(.split {variable} {left} {right})"


def render(manifest: dict, parent_job: dict, payloads: dict[str, str]) -> str:
    lines = [
        "import Proofs.Erdos85CnfBinarySplit",
        "import Proofs.Erdos85OrderFortyNineSevenHighT0CubeOneCover",
        "import Proofs.Erdos85OrderFortyNineLratCertificateBase", "",
        "/-! GENERATED checked binary tree below one h7/t0 cube-one parent. -/", "",
        "namespace Erdos85", "", "open Std Sat Std.Tactic.BVDecide", "",
    ]
    parent_cnf = parent_cnf_expression(parent_job)
    variables = manifest["split_variables"]
    for leaf in manifest["leaves"]:
        render_check(lines, leaf["id"],
                     branch_cnf(parent_cnf, variables, leaf["bits"]),
                     payloads[leaf["id"]])
    parent_id = manifest["parent_id"]
    tree_stem = lean_stem(parent_id + ".binary-tree")
    lines.extend([
        f"private theorem {tree_stem} : CnfBinaryCheckedTree ({parent_cnf}) :=",
        f"  {tree_expression(parent_id, variables)}", "",
        f"theorem {lean_stem(parent_id)}BinaryUnsat : ({parent_cnf}).Unsat :=",
        f"  CnfBinaryCheckedTree.unsat {tree_stem}", "",
        "end Erdos85", "",
    ])
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--ledger", type=Path, required=True)
    parser.add_argument("--certificate-dir", type=Path, required=True)
    parser.add_argument("--include-root", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    manifest, parent_job, payloads = load_and_validate(
        args.manifest.resolve(), args.ledger.resolve(),
        args.certificate_dir.resolve())
    portable = portable_include_paths(
        payloads, args.include_root.resolve(), args.output.resolve())
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(render(manifest, parent_job, portable))
    print(f"WROTE {args.output.resolve()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
