#!/usr/bin/env python3
"""Emit a checked Lean proof for one adaptive H7 binary-tree parent."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from generate_h7_adaptive_binary_tree_jobs import validate_bound_manifest
from generate_h7_t0_cube_one_cover_lean import (
    cnf_expression as parent_cnf_expression,
    lean_stem,
    portable_include_paths,
)
from generate_h7_t0_cube_one_mixed_lean import validate_payloads, render_check


def branch_cnf(base: str, nodes: dict[str, int], path: str) -> str:
    """Return the exact nested CNF fixed by ``path`` in an adaptive tree."""
    result = base
    for depth, bit in enumerate(path):
        variable = nodes[path[:depth]] - 1
        value = "true" if bit == "1" else "false"
        result = f"cnfWithSignedUnit ({result}) {variable} {value}"
    return result


def load_and_validate(manifest_path: Path, ledger: Path,
                      certificate_dir: Path) -> tuple[dict, dict, dict[str, Path]]:
    manifest = json.loads(manifest_path.read_text())
    base, _, leaves = validate_bound_manifest(manifest)
    parent = json.loads(Path(manifest["parent_manifest"]).read_text())
    matches = [job for job in parent["jobs"]
               if job.get("id") == manifest["parent_id"]]
    if len(matches) != 1:
        raise ValueError("adaptive parent is absent or duplicated")
    parent_job = matches[0]
    jobs = {
        leaf["id"]: (
            leaf["units"], manifest["base_clauses"] + len(leaf["units"]),
        )
        for leaf in leaves
    }
    payloads = validate_payloads(
        set(jobs), ledger, certificate_dir, jobs, base,
        manifest["variables"], manifest["base_clauses"])
    return manifest, parent_job, payloads


def tree_expression(parent_id: str, nodes: dict[str, int], path: str = "") -> str:
    """Render the unique checked tree derived from the prefix-node inventory."""
    if path not in nodes:
        leaf_id = f"{parent_id}.adaptive.leaf-{path}"
        return f"(.leaf {lean_stem(leaf_id)}Unsat)"
    variable = nodes[path] - 1
    left = tree_expression(parent_id, nodes, path + "0")
    right = tree_expression(parent_id, nodes, path + "1")
    return f"(.split {variable} {left} {right})"


def render(manifest: dict, parent_job: dict, payloads: dict[str, str]) -> str:
    lines = [
        "import Proofs.Erdos85CnfBinarySplit",
        "import Proofs.Erdos85OrderFortyNineSevenHighT0CubeOneCover",
        "import Proofs.Erdos85OrderFortyNineLratCertificateBase", "",
        "/-! GENERATED checked adaptive binary tree below one h7/t0 cube-one parent. -/", "",
        "namespace Erdos85", "", "open Std Sat Std.Tactic.BVDecide", "",
    ]
    parent_cnf = parent_cnf_expression(parent_job)
    nodes = manifest["nodes"]
    for leaf in manifest["leaves"]:
        render_check(lines, leaf["id"],
                     branch_cnf(parent_cnf, nodes, leaf["path"]),
                     payloads[leaf["id"]])
    parent_id = manifest["parent_id"]
    tree_stem = lean_stem(parent_id + ".adaptive-binary-tree")
    lines.extend([
        f"private theorem {tree_stem} : CnfBinaryCheckedTree ({parent_cnf}) :=",
        f"  {tree_expression(parent_id, nodes)}", "",
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
