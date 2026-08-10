#!/usr/bin/env python3
"""End-to-end provenance tests for exhaustive phase-cube aggregation."""

import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(path, doc):
    path.write_text(json.dumps(doc, indent=1) + "\n")


with tempfile.TemporaryDirectory() as raw:
    root = Path(raw)
    parent_cnf = root / "parent.cnf"
    parent_cnf.write_text(
        "p cnf 20000 4\n18349 18350 18351 0\n"
        "-18349 -18350 0\n-18349 -18351 0\n-18350 -18351 0\n")
    parent_manifest = root / "parent.manifest.json"
    write(parent_manifest, {"scope": "toy parent", "sha256": sha(parent_cnf)})
    parent_manifest_sha = sha(parent_manifest)
    for phase in range(3):
        stem = root / f"parent.anchor_o0c0_e2_p{phase}"
        cnf = Path(str(stem) + ".cnf")
        cnf.write_text(
            parent_cnf.read_text().replace("p cnf 20000 4\n", "p cnf 20000 5\n")
            + f"{18349 + phase} 0\n")
        manifest = Path(str(stem) + ".manifest.json")
        write(manifest, {
            "parent_manifest_sha256": parent_manifest_sha,
            "parent_cnf_sha256": sha(parent_cnf),
            "sha256": sha(cnf), "cube_phase": phase,
            "cube_literal": 18349 + phase,
            "exhaustive_anchor_literals": [18349, 18350, 18351],
            "exhaustive_clause_verified": True,
            "mutual_exclusion_clauses_verified": True,
            "cube_partition_verified": True,
        })
        cert_dir = root / f"cert-{phase}"
        cert_dir.mkdir()
        proof = cert_dir / "proof.drat"
        proof.write_text(f"proof {phase}\n")
        log = cert_dir / "drat-trim.log"
        log.write_text("c checked\ns VERIFIED\n")
        cert = cert_dir / "certificate.json"
        write(cert, {
            "verdict": "SYMBOLIC_CLASS_UNSAT_DRAT_VERIFIED",
            "cnf_sha256": sha(cnf), "manifest_sha256": sha(manifest),
            "proof": str(proof), "proof_sha256": sha(proof),
            "drat_trim_command": ["drat-trim", str(cnf), str(proof)],
            "drat_trim_exit": 0, "drat_trim_log_sha256": sha(log),
        })

    script = Path(__file__).with_name("summarize_symbolic_phase_cubes.py")
    output = root / "summary.json"
    subprocess.run([sys.executable, str(script), str(parent_manifest), str(root),
                    "--output", str(output)], check=True)
    report = json.loads(output.read_text())
    assert report["verdict"] == (
        "SYMBOLIC_PARENT_UNSAT_BY_EXHAUSTIVE_DRAT_VERIFIED_CUBES")
    assert [item["phase"] for item in report["cube_certificates"]] == [0, 1, 2]

    missing = root / "cert-2" / "certificate.json"
    missing.rename(missing.with_suffix(".absent"))
    failed = subprocess.run(
        [sys.executable, str(script), str(parent_manifest), str(root),
         "--output", str(root / "bad.json")], capture_output=True, text=True)
    assert failed.returncode != 0
    assert "missing verified certificate phase(s): [2]" in failed.stderr

print("SYMBOLIC PHASE CUBE SUMMARY ALL OK")
