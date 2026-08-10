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
    residue_domain = [mapping[((0, 1), 2, p)] for p in range(12)]
    next_residue_domain = [mapping[((0, 2), 2, p)] for p in range(12)]
    clauses = (anchor_clauses(first) + anchor_clauses(second) +
               anchor_clauses(residue_domain) +
               anchor_clauses(next_residue_domain))
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
    # The production root split predates explicit cube_anchor/cube_ancestry
    # metadata.  Its other partition fields remain exact and sufficient for a
    # narrowly scoped legacy-root upgrade in the verifier.
    for top_manifest in top_manifests:
        top_doc = json.loads(top_manifest.read_text())
        top_doc.pop("cube_anchor")
        top_doc.pop("cube_ancestry")
        write(top_manifest, top_doc)
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
            if (phase, q) == (1, 1):
                residue_dir = root / "p1-q1-residues"
                residue_splitter = Path(__file__).with_name(
                    "split_symbolic_phase_residue.py")
                child_cnf = child_manifest.with_suffix("").with_suffix(".cnf")
                subprocess.run([
                    sys.executable, str(residue_splitter), str(child_manifest),
                    str(child_cnf), str(residue_dir),
                    "--anchor", "0", "1", "2",
                ], check=True, capture_output=True, text=True)
                for residue, residue_manifest in enumerate(sorted(
                        residue_dir.glob("*.manifest.json"))):
                    if residue == 1:
                        value_dir = root / "p1-q1-r1-values"
                        value_splitter = Path(__file__).with_name(
                            "split_symbolic_phase_value.py")
                        residue_cnf = residue_manifest.with_suffix(
                            "").with_suffix(".cnf")
                        subprocess.run([
                            sys.executable, str(value_splitter),
                            str(residue_manifest), str(residue_cnf),
                            str(value_dir), "--anchor", "0", "1", "2",
                        ], check=True, capture_output=True, text=True)
                        for value_manifest in sorted(
                                value_dir.glob("*.manifest.json")):
                            value = json.loads(
                                value_manifest.read_text())["cube_value"]
                            fake_certificate(
                                value_manifest,
                                root / f"cert-p1-q1-r1-v{value}")
                    else:
                        fake_certificate(residue_manifest,
                                         root / f"cert-p1-q1-r{residue}")
            else:
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
        "--residue-anchor", "0", "1", "2",
        "--value-anchor", "0", "1", "2",
        "--output", str(output),
    ], check=True)
    report = json.loads(output.read_text())
    assert report["verdict"] == (
        "SYMBOLIC_ROOT_UNSAT_BY_RECURSIVE_EXHAUSTIVE_DRAT_TREE")
    assert report["evidence"]["children"][0]["evidence"]["kind"] == (
        "verified_drat_leaf")
    assert report["evidence"]["children"][1]["evidence"]["kind"] == (
        "exhaustive_phase_partition")
    assert report["evidence"]["children"][1]["evidence"]["children"][1][
        "evidence"]["kind"] == "exhaustive_phase_residue_partition"
    assert report["evidence"]["children"][1]["evidence"]["children"][1][
        "evidence"]["children"][1]["evidence"]["kind"] == (
            "exhaustive_phase_value_partition")
    missing = root / "cert-p1-q1-r1-v10" / "certificate.json"
    missing.rename(missing.with_suffix(".absent"))
    rejected = subprocess.run([
        sys.executable, str(verifier), str(manifest), str(root),
        "--anchor", "0", "0", "2", "--anchor", "1", "0", "2",
        "--residue-anchor", "0", "1", "2",
        "--value-anchor", "0", "1", "2",
        "--output", str(root / "incomplete.json"),
    ], capture_output=True, text=True)
    assert rejected.returncode != 0
    assert "uncertified leaf" in rejected.stderr

    # The production refinement order now needs a second residue partition
    # after an exact-value partition.  Replace the direct value certificates
    # with residue children and exercise the ordered split CLI, which can
    # represent phase -> residue -> value -> residue interleaving.
    missing.with_suffix(".absent").rename(missing)
    next_residue_splitter = Path(__file__).with_name(
        "split_symbolic_phase_residue.py")
    for value_manifest in sorted(value_dir.glob("*.manifest.json")):
        value = json.loads(value_manifest.read_text())["cube_value"]
        direct = root / f"cert-p1-q1-r1-v{value}" / "certificate.json"
        direct.rename(direct.with_suffix(".direct"))
        next_dir = root / f"p1-q1-r1-v{value}-residues"
        subprocess.run([
            sys.executable, str(next_residue_splitter), str(value_manifest),
            str(value_manifest.with_suffix("").with_suffix(".cnf")),
            str(next_dir), "--anchor", "0", "2", "2",
        ], check=True, capture_output=True, text=True)
        for next_residue, next_manifest in enumerate(sorted(
                next_dir.glob("*.manifest.json"))):
            fake_certificate(
                next_manifest,
                root / f"cert-p1-q1-r1-v{value}-s{next_residue}")

    ordered_output = root / "ordered-tree-report.json"
    subprocess.run([
        sys.executable, str(verifier), str(manifest), str(root),
        "--split", "phase:0,0,2", "--split", "phase:1,0,2",
        "--split", "residue:0,1,2", "--split", "value:0,1,2",
        "--split", "residue:0,2,2", "--output", str(ordered_output),
    ], check=True)
    ordered_report = json.loads(ordered_output.read_text())
    assert [entry["kind"] for entry in ordered_report["ordered_splits"]] == [
        "phase", "phase", "residue", "value", "residue"]
    ordered_value = ordered_report["evidence"]["children"][1]["evidence"][
        "children"][1]["evidence"]["children"][1]["evidence"][
        "children"][0]["evidence"]
    assert ordered_value["kind"] == "exhaustive_phase_residue_partition"

print("SYMBOLIC PHASE TREE SUMMARY ALL OK")
