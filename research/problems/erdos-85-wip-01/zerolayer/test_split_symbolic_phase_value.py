#!/usr/bin/env python3
"""End-to-end checks for exact-value refinement of residue cubes."""

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


with tempfile.TemporaryDirectory() as raw:
    root = Path(raw)
    mapping, _ = phase_variable_map()
    literals = [mapping[(0, 1), 2, phase] for phase in range(12)]
    clauses = [" ".join(map(str, literals)) + " 0"]
    clauses.extend(f"-{a} -{b} 0" for a, b in combinations(literals, 2))
    cnf = root / "root.cnf"
    cnf.write_text(f"p cnf 20000 {len(clauses)}\n" +
                   "\n".join(clauses) + "\n")
    manifest = root / "root.manifest.json"
    manifest.write_text(json.dumps({
        "scope": "toy root", "sha256": sha(cnf), "vars": 20000,
        "clauses": len(clauses), "encoder_sha256": "e" * 64,
        "sat_verifier_sha256": "v" * 64,
        "rule_counts": {"toy": len(clauses)},
        "options": {"phase_symmetry": True},
    }, indent=1) + "\n")

    residue_splitter = Path(__file__).with_name(
        "split_symbolic_phase_residue.py")
    residue_dir = root / "residues"
    subprocess.run([
        sys.executable, str(residue_splitter), str(manifest), str(cnf),
        str(residue_dir), "--anchor", "0", "1", "2",
    ], check=True, capture_output=True, text=True)
    residue_manifest = sorted(residue_dir.glob("*.manifest.json"))[1]
    residue_cnf = residue_manifest.with_suffix("").with_suffix(".cnf")

    value_splitter = Path(__file__).with_name(
        "split_symbolic_phase_value.py")
    value_dir = root / "values"
    run = subprocess.run([
        sys.executable, str(value_splitter), str(residue_manifest),
        str(residue_cnf), str(value_dir), "--anchor", "0", "1", "2",
    ], check=True, capture_output=True, text=True)
    summary = json.loads(run.stdout)
    assert summary["value_literals"] == literals[1::3]
    assert [item["value"] for item in summary["cubes"]] == [1, 4, 7, 10]
    for item in summary["cubes"]:
        child_cnf = Path(item["cnf"])
        child_manifest = json.loads(Path(item["manifest"]).read_text())
        assert sha(child_cnf) == child_manifest["sha256"] == item["sha256"]
        assert child_manifest["cube_value"] == item["value"]
        assert child_cnf.read_text().splitlines()[-1] == (
            f"{child_manifest['cube_literal']} 0")

    subprocess.run([
        sys.executable, str(value_splitter), str(residue_manifest),
        str(residue_cnf), str(value_dir), "--anchor", "0", "1", "2",
        "--reuse-existing-cnfs",
    ], check=True, capture_output=True, text=True)

    bad_doc = json.loads(residue_manifest.read_text())
    bad_doc["cube_clause_literals"] = literals[2::3]
    bad_manifest = root / "bad.manifest.json"
    bad_manifest.write_text(json.dumps(bad_doc, indent=1) + "\n")
    rejected = subprocess.run([
        sys.executable, str(value_splitter), str(bad_manifest),
        str(residue_cnf), str(root / "bad-values"),
        "--anchor", "0", "1", "2",
    ], capture_output=True, text=True)
    assert rejected.returncode != 0
    assert "residue literals" in rejected.stderr

print("SYMBOLIC PHASE VALUE SPLITTER ALL OK")
