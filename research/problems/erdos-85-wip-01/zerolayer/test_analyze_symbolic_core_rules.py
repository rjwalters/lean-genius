#!/usr/bin/env python3
"""End-to-end toy test for symbolic core-to-rule mapping."""

import json
from pathlib import Path
import subprocess
import sys
import tempfile


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
        "rule_counts": {"first": 2, "second": 2, "unit": 1},
    }))
    output = root / "report.json"
    script = Path(__file__).with_name("analyze_symbolic_core_rules.py")
    subprocess.run([sys.executable, str(script), str(manifest), str(cnf),
                    str(core), "--output", str(output)], check=True,
                   capture_output=True, text=True)
    report = json.loads(output.read_text())
    assert report["core_clauses"] == 3
    assert [item["core_clauses"] for item in report["families"]] == [1, 1, 1]

print("SYMBOLIC CORE RULE MAPPER ALL OK")
