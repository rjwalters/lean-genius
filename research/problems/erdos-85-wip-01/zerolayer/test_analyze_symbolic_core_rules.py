#!/usr/bin/env python3
"""End-to-end toy test for symbolic core-to-rule mapping."""

import json
from pathlib import Path
import subprocess
import sys
import tempfile


def sha(path):
    import hashlib
    return hashlib.sha256(path.read_bytes()).hexdigest()


with tempfile.TemporaryDirectory() as raw:
    root = Path(raw)
    cnf = root / "toy.cnf"
    cnf.write_text("p cnf 4 5\n1 2 0\n-1 3 0\n4 0\n-4 2 0\n-2 0\n")
    core = root / "core.cnf"
    # Reorder the first clause's literals to exercise normalization.
    core.write_text("p cnf 4 3\n2 1 0\n4 0\n-2 0\n")
    manifest = root / "toy.manifest.json"
    manifest.write_text(json.dumps({
        "clauses": 5,
        "sha256": sha(cnf),
        "rule_counts": {"first": 2, "second": 2, "unit": 1},
    }))
    output = root / "report.json"
    script = Path(__file__).with_name("analyze_symbolic_core_rules.py")
    subprocess.run([sys.executable, str(script), str(manifest), str(cnf),
                    str(core), "--output", str(output)], check=True,
                   capture_output=True, text=True)
    report = json.loads(output.read_text())
    assert report["core_clauses"] == 3
    assert report["cnf_sha256"] == sha(cnf)
    assert report["core_sha256"] == sha(core)
    assert [item["core_clauses"] for item in report["families"]] == [1, 1, 1]

    bad_manifest = root / "bad.manifest.json"
    bad_manifest.write_text(json.dumps({
        "clauses": 5, "sha256": "0" * 64,
        "rule_counts": {"first": 2, "second": 2, "unit": 1},
    }))
    rejected = subprocess.run(
        [sys.executable, str(script), str(bad_manifest), str(cnf), str(core)],
        capture_output=True, text=True)
    assert rejected.returncode != 0
    assert "CNF hash does not match manifest" in rejected.stderr

print("SYMBOLIC CORE RULE MAPPER ALL OK")
