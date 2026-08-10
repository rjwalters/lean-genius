#!/usr/bin/env python3
"""Verify a recursive phase-cube certificate tree from leaves to root."""

import argparse
import json
from pathlib import Path

from run_hlift_orbit_signal import sha256_file
from split_symbolic_phase_residue import expected_clause_sha256
from summarize_symbolic_phase_cubes import (
    VERIFIED, expected_cube_hashes, load, require_exact_command, require_hash,
    require_relocatable_artifact, verified_log,
)
from verify_symbolic_hlift_assignment import phase_variable_map


def validate_certificate(cert_path, manifest_path, manifest, cnf):
    cert = load(cert_path)
    if cert.get("verdict") != VERIFIED:
        raise ValueError(f"certificate is not DRAT-verified: {cert_path}")
    if cert.get("cnf_sha256") != manifest["sha256"]:
        raise ValueError(f"certificate CNF hash mismatch: {cert_path}")
    if cert.get("manifest_sha256") != sha256_file(manifest_path):
        raise ValueError(f"certificate manifest mismatch: {cert_path}")
    recorded_cnf = Path(cert.get("cnf", "")).resolve()
    if recorded_cnf.name != cnf.name:
        raise ValueError(f"certificate CNF path mismatch: {cert_path}")
    recorded_proof = Path(cert["proof"]).resolve()
    require_relocatable_artifact(
        cert["proof"], cert_path.parent, cert["proof_sha256"], "proof")
    require_exact_command(cert.get("solver_command"), recorded_cnf,
                          recorded_proof, "solver")
    require_exact_command(cert.get("drat_trim_command"), recorded_cnf,
                          recorded_proof,
                          "drat-trim")
    log_path = cert_path.parent / "drat-trim.log"
    require_hash(log_path, cert["drat_trim_log_sha256"], "drat-trim log")
    if cert.get("drat_trim_exit") != 0 or not verified_log(log_path):
        raise ValueError(f"failed DRAT verification evidence: {cert_path}")
    return {"certificate": str(cert_path),
            "certificate_sha256": sha256_file(cert_path)}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("root_manifest", type=Path)
    parser.add_argument("artifact_dir", type=Path)
    parser.add_argument("--anchor", action="append", nargs=3, type=int,
                        metavar=("OMIT", "COPY", "COMPONENT"), required=True)
    parser.add_argument("--residue-anchor", action="append", nargs=3, type=int,
                        metavar=("OMIT", "COPY", "COMPONENT"), default=[])
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    root_manifest = args.root_manifest.resolve()
    artifact_dir = args.artifact_dir.resolve()
    manifests = list(artifact_dir.glob("**/*.manifest.json"))
    children_by_parent = {}
    for path in manifests:
        parent_sha = load(path).get("parent_manifest_sha256")
        if parent_sha:
            children_by_parent.setdefault(parent_sha, []).append(path.resolve())
    certificates = list(artifact_dir.glob("**/certificate.json"))
    mapping, _ = phase_variable_map()
    split_specs = ([('phase', tuple(anchor)) for anchor in args.anchor] +
                   [('residue', tuple(anchor))
                    for anchor in args.residue_anchor])

    def visit(manifest_path, depth):
        manifest_path = manifest_path.resolve()
        manifest = load(manifest_path)
        manifest_sha = sha256_file(manifest_path)
        cnf = require_hash(manifest_path.with_suffix("").with_suffix(".cnf"),
                           manifest["sha256"], "tree-node CNF")
        direct = [path.resolve() for path in certificates
                  if load(path).get("cnf_sha256") == manifest["sha256"] and
                  load(path).get("manifest_sha256") == manifest_sha]
        if direct:
            if len(direct) != 1:
                raise ValueError(f"duplicate direct certificates for {manifest_path}")
            return {"kind": "verified_drat_leaf", "manifest": str(manifest_path),
                    **validate_certificate(direct[0], manifest_path, manifest, cnf)}
        if depth == len(split_specs):
            raise ValueError(f"uncertified leaf: {manifest_path}")

        split_kind, (omit, copy, component) = split_specs[depth]
        if split_kind == "residue":
            try:
                exact_literals = [mapping[((omit, copy), component, phase)]
                                  for phase in range(12)]
            except KeyError as exc:
                raise ValueError(
                    f"invalid residue anchor: {(omit, copy, component)}") from exc
            anchor_name = f"tau[({omit},{copy}),{component}]"
            residue_literals = [
                [exact_literals[phase] for phase in range(residue, 12, 3)]
                for residue in range(3)
            ]
            expected_hashes = [
                expected_clause_sha256(cnf, manifest["vars"],
                                       manifest["clauses"], branch)
                for branch in residue_literals
            ]
            candidates = children_by_parent.get(manifest_sha, [])
            by_residue = {}
            for child_path in candidates:
                child = load(child_path)
                if child.get("cube_anchor") != anchor_name:
                    continue
                residue = child.get("cube_residue")
                if residue not in range(3) or residue in by_residue:
                    raise ValueError(
                        f"bad or duplicate child residue at {manifest_path}")
                if child.get("scope") != (
                        manifest["scope"] + f" AND {anchor_name}%3={residue}"):
                    raise ValueError(f"child scope mismatch: {child_path}")
                if (child.get("parent_cnf_sha256") != manifest["sha256"] or
                        child.get("cube_residue_modulus") != 3 or
                        child.get("cube_clause_literals") !=
                        residue_literals[residue] or
                        child.get("exact_phase_literals") != exact_literals or
                        not child.get("exact_one_hot_verified") or
                        not child.get("exact_pairwise_exclusions_verified") or
                        not child.get("cube_partition_verified") or
                        child.get("sha256") != expected_hashes[residue]):
                    raise ValueError(
                        f"invalid residue child transformation: {child_path}")
                require_hash(child_path.with_suffix("").with_suffix(".cnf"),
                             child["sha256"], "residue child CNF")
                by_residue[residue] = child_path
            if set(by_residue) != set(range(3)):
                raise ValueError(
                    f"missing child residues at {manifest_path}: "
                    f"{sorted(by_residue)}")
            return {
                "kind": "exhaustive_phase_residue_partition",
                "manifest": str(manifest_path),
                "anchor": anchor_name,
                "exact_phase_literals": exact_literals,
                "residue_literals": residue_literals,
                "children": [
                    {"residue": residue,
                     "evidence": visit(by_residue[residue], depth + 1)}
                    for residue in range(3)
                ],
            }

        try:
            literals = [mapping[((omit, copy), component, phase)]
                        for phase in range(3)]
        except KeyError as exc:
            raise ValueError(f"invalid phase anchor: {args.anchor[depth]}") from exc
        anchor_name = f"tau[({omit},{copy}),{component}]"
        expected_hashes = expected_cube_hashes(cnf, literals)
        candidates = children_by_parent.get(manifest_sha, [])
        by_phase = {}
        for child_path in candidates:
            child = load(child_path)
            child_anchor = child.get("cube_anchor")
            legacy_root_child = (
                depth == 0 and child_anchor is None and
                child.get("cube_ancestry") is None)
            if child_anchor != anchor_name and not legacy_root_child:
                continue
            phase = child.get("cube_phase")
            if phase not in range(3) or phase in by_phase:
                raise ValueError(f"bad or duplicate child phase at {manifest_path}")
            if child.get("scope") != manifest["scope"] + f" AND {anchor_name}={phase}":
                raise ValueError(f"child scope mismatch: {child_path}")
            if (child.get("parent_cnf_sha256") != manifest["sha256"] or
                    child.get("exhaustive_anchor_literals") != literals or
                    child.get("cube_literal") != literals[phase] or
                    not child.get("cube_partition_verified") or
                    child.get("sha256") != expected_hashes[phase]):
                raise ValueError(f"invalid child transformation: {child_path}")
            require_hash(child_path.with_suffix("").with_suffix(".cnf"),
                         child["sha256"], "child CNF")
            by_phase[phase] = child_path
        if set(by_phase) != set(range(3)):
            raise ValueError(f"missing child phases at {manifest_path}: {sorted(by_phase)}")
        return {"kind": "exhaustive_phase_partition",
                "manifest": str(manifest_path), "anchor": anchor_name,
                "anchor_literals": literals,
                "children": [{"phase": phase, "evidence": visit(by_phase[phase], depth + 1)}
                             for phase in range(3)]}

    evidence = visit(root_manifest, 0)
    report = {
        "verdict": "SYMBOLIC_ROOT_UNSAT_BY_RECURSIVE_EXHAUSTIVE_DRAT_TREE",
        "root_manifest": str(root_manifest),
        "root_manifest_sha256": sha256_file(root_manifest),
        "root_cnf_sha256": load(root_manifest)["sha256"],
        "anchors": [f"tau[({o},{c}),{e}]" for o, c, e in args.anchor],
        "residue_anchors": [f"tau[({o},{c}),{e}]%3"
                            for o, c, e in args.residue_anchor],
        "evidence": evidence,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=1) + "\n")
    print(report["verdict"], args.output)


if __name__ == "__main__":
    main()
