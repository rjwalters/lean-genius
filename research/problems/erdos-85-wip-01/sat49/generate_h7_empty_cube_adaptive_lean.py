#!/usr/bin/env python3
"""Validate an adaptive H7 LRAT tree and emit its checked Lean evidence."""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import os
import re
from pathlib import Path

import generate_h7_empty_cube_adaptive_split_jobs as adaptive
import generate_h7_empty_cube_lean as mixed
import generate_h7_empty_cube_manifest as parents


RECEIPT_RE = re.compile(
    r"(cube_F(\d+)_t(\d+)\.adaptive\.leaf-([01]+))\s+"
    r"([0-9a-f]{64})\s+([0-9a-f]{64})\s+(\d+)$")


def read_receipts(path: Path) -> dict[str, dict[str, object]]:
    result = {}
    for number, raw in enumerate(path.read_text().splitlines(), 1):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        match = RECEIPT_RE.fullmatch(line)
        if match is None:
            raise ValueError(f"{path}:{number}: malformed adaptive receipt")
        job_id, edge_count, type_index, leaf_path, cnf_hash, proof_hash, size = (
            match.groups())
        if job_id in result:
            raise ValueError(f"duplicate adaptive receipt: {job_id}")
        result[job_id] = {
            "edge_count": int(edge_count), "type_index": int(type_index),
            "path": leaf_path, "cnf_sha256": cnf_hash,
            "lrat_gz_sha256": proof_hash, "lrat_gz_bytes": int(size),
        }
    return result


def validate_and_unpack(parent_manifest: dict, parent_hash: str,
                        spec: dict, spec_hash: str, manifest: dict,
                        receipts: dict[str, dict[str, object]], base: Path,
                        certificate_dir: Path,
                        proof_dir: Path) -> tuple[dict, dict[str, int], list[dict],
                                                   dict[str, Path]]:
    expected = adaptive.build_manifest(
        parent_manifest, parent_hash, spec, spec_hash, base)
    if manifest != expected:
        raise ValueError("adaptive manifest differs from bound inputs")
    leaves = expected["leaves"]
    leaf_ids = {leaf["id"] for leaf in leaves}
    if set(receipts) != leaf_ids:
        raise ValueError("adaptive receipt inventory has missing or surplus leaves")
    payloads = {}
    for leaf in leaves:
        leaf_id = leaf["id"]
        receipt = receipts[leaf_id]
        if (receipt["edge_count"] != expected["edge_count"] or
                receipt["type_index"] != expected["type_index"] or
                receipt["path"] != leaf["path"]):
            raise ValueError(f"adaptive receipt parent/path mismatch: {leaf_id}")
        cnf_hash, _ = mixed._leaf_identity(parent_manifest, base, leaf["units"])
        if receipt["cnf_sha256"] != cnf_hash:
            raise ValueError(f"adaptive CNF receipt mismatch: {leaf_id}")
        payload = mixed._gzip_payload(certificate_dir, leaf_id, receipt)
        unpacked = proof_dir / f"{leaf_id}.lrat"
        mixed._unpack(payload, unpacked)
        payloads[leaf_id] = unpacked.resolve()
    return expected, expected["nodes"], leaves, payloads


def _cnf_expr(edge_count: int, type_index: int, path: str,
              nodes: dict[str, int]) -> str:
    result = ("orderFortyNineSevenHighT0CanonicalEmptyCubeSatCnf "
              f"{edge_count} {type_index}")
    for depth, bit in enumerate(path):
        result = (f"cnfWithSignedUnit ({result}) "
                  f"{nodes[path[:depth]] - 1} "
                  f"{'true' if bit == '1' else 'false'}")
    return result


def _tree_expr(parent_id: str, path: str, nodes: dict[str, int]) -> str:
    if path not in nodes:
        stem = mixed.lean_stem(f"{parent_id}.adaptive.leaf-{path}")
        return f".leaf (LRAT.check_sound {stem}Proof _ {stem}Check)"
    return (f".split {nodes[path] - 1} "
            f"({_tree_expr(parent_id, path + '0', nodes)}) "
            f"({_tree_expr(parent_id, path + '1', nodes)})")


def render(manifest: dict, nodes: dict[str, int], leaves: list[dict],
           includes: dict[str, str]) -> str:
    edge_count, type_index = manifest["edge_count"], manifest["type_index"]
    parent_id = manifest["parent_id"]
    lines = [
        "import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalEmptyCubeSplitTerminal",
        "import Proofs.Erdos85OrderFortyNineLratCertificateBase", "",
        "/-! GENERATED checked adaptive evidence for one canonical H7 empty cube. -/",
        "", "namespace Erdos85", "", "open Std Sat Std.Tactic.BVDecide", "",
    ]
    for leaf in leaves:
        leaf_id, path = leaf["id"], leaf["path"]
        stem = mixed.lean_stem(leaf_id)
        lines += [
            f"private def {stem}Proof : Array LRAT.IntAction :=",
            "  parseOrderFortyNineLratProof",
            f"    (include_str {json.dumps(includes[leaf_id])})", "",
            "set_option maxHeartbeats 0 in", "set_option maxRecDepth 1000000 in",
            f"private theorem {stem}Check : LRAT.check {stem}Proof",
            f"    ({_cnf_expr(edge_count, type_index, path, nodes)}) := by",
            "  native_decide", "",
        ]
    evidence_name = f"h7EmptyAdaptiveEvidenceF{edge_count}T{type_index}"
    lines += [
        f"def {evidence_name} :",
        "    SevenHighT0CanonicalEmptyCubeLratEvidence "
        f"{edge_count} {type_index} :=",
        f"  .binaryTree ({_tree_expr(parent_id, '', nodes)})", "",
        "end Erdos85", "",
        f"#print axioms Erdos85.{evidence_name}", "",
    ]
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--parent-manifest", type=Path, required=True)
    parser.add_argument("--tree-spec", type=Path, required=True)
    parser.add_argument("--adaptive-manifest", type=Path, required=True)
    parser.add_argument("--base", type=Path, required=True)
    parser.add_argument("--receipts", type=Path, required=True)
    parser.add_argument("--certificate-dir", type=Path, required=True)
    parser.add_argument("--proof-output-dir", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    parent_manifest = json.loads(args.parent_manifest.read_text())
    spec = json.loads(args.tree_spec.read_text())
    manifest = json.loads(args.adaptive_manifest.read_text())
    bound, nodes, leaves, payloads = validate_and_unpack(
        parent_manifest, parents.sha256(args.parent_manifest), spec,
        parents.sha256(args.tree_spec), manifest, read_receipts(args.receipts),
        args.base, args.certificate_dir, args.proof_output_dir)
    includes = {key: os.path.relpath(path, args.output.resolve().parent)
                for key, path in payloads.items()}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(render(bound, nodes, leaves, includes))
    print(f"WROTE {args.output} ({len(leaves)} adaptive LRAT leaves)")


if __name__ == "__main__":
    main()
