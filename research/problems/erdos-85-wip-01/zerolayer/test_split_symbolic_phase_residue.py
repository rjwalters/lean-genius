#!/usr/bin/env python3
"""End-to-end checks for the certified exact-phase residue splitter."""

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
        "scope": "toy root",
        "sha256": sha(cnf),
        "vars": 20000,
        "clauses": len(clauses),
        "encoder_sha256": "e" * 64,
        "sat_verifier_sha256": "v" * 64,
        "rule_counts": {"toy": len(clauses)},
        "options": {"phase_symmetry": True},
    }, indent=1) + "\n")
    splitter = Path(__file__).with_name("split_symbolic_phase_residue.py")
    output = root / "children"
    run = subprocess.run([
        sys.executable, str(splitter), str(manifest), str(cnf), str(output),
        "--anchor", "0", "1", "2",
    ], check=True, capture_output=True, text=True)
    summary = json.loads(run.stdout)
    assert summary["residue_partition_verified"]
    assert len(summary["cubes"]) == 3
    for residue, item in enumerate(summary["cubes"]):
        child_cnf = Path(item["cnf"])
        child_manifest = Path(item["manifest"])
        doc = json.loads(child_manifest.read_text())
        expected = [literals[phase] for phase in range(residue, 12, 3)]
        assert doc["cube_residue"] == residue
        assert doc["cube_clause_literals"] == expected
        assert doc["sha256"] == sha(child_cnf) == item["sha256"]
        assert child_cnf.read_text().splitlines()[-1] == (
            " ".join(map(str, expected)) + " 0")

    subprocess.run([
        sys.executable, str(splitter), str(manifest), str(cnf), str(output),
        "--anchor", "0", "1", "2", "--reuse-existing-cnfs",
    ], check=True, capture_output=True, text=True)

    bad = root / "bad.cnf"
    bad_text = cnf.read_text().replace(clauses[-1] + "\n", "")
    bad_text = bad_text.replace(f"p cnf 20000 {len(clauses)}\n",
                                f"p cnf 20000 {len(clauses) - 1}\n")
    bad.write_text(bad_text)
    bad_manifest = json.loads(manifest.read_text())
    bad_manifest["sha256"] = sha(bad)
    bad_manifest["clauses"] -= 1
    bad_manifest_path = root / "bad.manifest.json"
    bad_manifest_path.write_text(json.dumps(bad_manifest, indent=1) + "\n")
    rejected = subprocess.run([
        sys.executable, str(splitter), str(bad_manifest_path), str(bad),
        str(root / "bad-children"), "--anchor", "0", "1", "2",
    ], capture_output=True, text=True)
    assert rejected.returncode != 0
    assert "exclusion clause" in rejected.stderr

print("SYMBOLIC PHASE RESIDUE SPLITTER ALL OK")
