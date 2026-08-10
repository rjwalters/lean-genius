#!/usr/bin/env python3
"""End-to-end mixed-depth test for recursive phase-tree verification."""

import hashlib
import json
from itertools import combinations
from pathlib import Path
import subprocess
import sys
import tempfile

from verify_symbolic_hlift_assignment import phase_variable_map


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(path, doc):
    path.write_text(json.dumps(doc, indent=1) + "\n")


def anchor_clauses(literals):
    return [" ".join(map(str, literals)) + " 0",
            *(f"-{a} -{b} 0" for a, b in combinations(literals, 2))]


def fake_certificate(manifest_path, phase_dir):
    manifest = json.loads(manifest_path.read_text())
    cnf = manifest_path.with_suffix("").with_suffix(".cnf").resolve()
    phase_dir.mkdir()
    proof = phase_dir / "proof.drat"
    proof.write_text("toy proof\n")
    log = phase_dir / "drat-trim.log"
    log.write_text("s VERIFIED\n")
    write(phase_dir / "certificate.json", {
        "verdict": "SYMBOLIC_CLASS_UNSAT_DRAT_VERIFIED",
        "cnf": str(cnf), "cnf_sha256": manifest["sha256"],
        "manifest_sha256": sha(manifest_path),
        "proof": str(proof.resolve()), "proof_sha256": sha(proof),
        "solver_command": ["kissat", str(cnf), str(proof.resolve())],
        "drat_trim_command": ["drat-trim", str(cnf), str(proof.resolve())],
        "drat_trim_exit": 0, "drat_trim_log_sha256": sha(log),
    })


with tempfile.TemporaryDirectory() as raw:
    root = Path(raw)
    mapping, _ = phase_variable_map()
    first = [mapping[((0, 0), 2, p)] for p in range(3)]
    second = [mapping[((1, 0), 2, p)] for p in range(3)]
    clauses = anchor_clauses(first) + anchor_clauses(second)
    cnf = root / "root.cnf"
    cnf.write_text(f"p cnf 20000 {len(clauses)}\n" + "\n".join(clauses) + "\n")
    manifest = root / "root.manifest.json"
    write(manifest, {
        "scope": "toy root", "sha256": sha(cnf), "vars": 20000,
        "clauses": len(clauses), "encoder_sha256": "e" * 64,
        "sat_verifier_sha256": "v" * 64,
        "rule_counts": {"toy": len(clauses)},
        "options": {"phase_symmetry": True},
    })
    splitter = Path(__file__).with_name("split_symbolic_phase_anchor.py")
    top = root / "top"
    subprocess.run([sys.executable, str(splitter), str(manifest), str(cnf),
                    str(top)], check=True, capture_output=True, text=True)
    top_manifests = sorted(top.glob("*.manifest.json"))
    fake_certificate(top_manifests[0], root / "cert-p0")
    for phase in (1, 2):
        child_dir = root / f"p{phase}-children"
        parent_manifest = top_manifests[phase]
        parent_cnf = parent_manifest.with_suffix("").with_suffix(".cnf")
        subprocess.run([
            sys.executable, str(splitter), str(parent_manifest), str(parent_cnf),
            str(child_dir), "--anchor", "1", "0", "2",
        ], check=True, capture_output=True, text=True)
        for q, child_manifest in enumerate(sorted(child_dir.glob("*.manifest.json"))):
            fake_certificate(child_manifest, root / f"cert-p{phase}-q{q}")

    # Certificates remain verifiable after archival relocation: their exact
    # original commands are retained, while adjacent hash-identical artifacts
    # satisfy the current tree.
    relocated = root / "cert-p1-q0" / "certificate.json"
    relocated_doc = json.loads(relocated.read_text())
    remote_cnf = Path("/remote/original") / Path(relocated_doc["cnf"]).name
    remote_proof = Path("/remote/original/proof.drat")
    relocated_doc["cnf"] = str(remote_cnf)
    relocated_doc["proof"] = str(remote_proof)
    relocated_doc["solver_command"] = ["kissat", str(remote_cnf),
                                         str(remote_proof)]
    relocated_doc["drat_trim_command"] = ["drat-trim", str(remote_cnf),
                                            str(remote_proof)]
    write(relocated, relocated_doc)

    verifier = Path(__file__).with_name("summarize_symbolic_phase_tree.py")
    output = root / "tree-report.json"
    subprocess.run([
        sys.executable, str(verifier), str(manifest), str(root),
        "--anchor", "0", "0", "2", "--anchor", "1", "0", "2",
        "--output", str(output),
    ], check=True)
    report = json.loads(output.read_text())
    assert report["verdict"] == (
        "SYMBOLIC_ROOT_UNSAT_BY_RECURSIVE_EXHAUSTIVE_DRAT_TREE")
    assert report["evidence"]["children"][0]["evidence"]["kind"] == (
        "verified_drat_leaf")
    assert report["evidence"]["children"][1]["evidence"]["kind"] == (
        "exhaustive_phase_partition")
    missing = root / "cert-p2-q2" / "certificate.json"
    missing.rename(missing.with_suffix(".absent"))
    rejected = subprocess.run([
        sys.executable, str(verifier), str(manifest), str(root),
        "--anchor", "0", "0", "2", "--anchor", "1", "0", "2",
        "--output", str(root / "incomplete.json"),
    ], capture_output=True, text=True)
    assert rejected.returncode != 0
    assert "uncertified leaf" in rejected.stderr

print("SYMBOLIC PHASE TREE SUMMARY ALL OK")
