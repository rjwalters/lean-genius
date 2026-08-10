#!/usr/bin/env python3
"""Small end-to-end test for the exhaustive phase-anchor cube splitter."""

import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


with tempfile.TemporaryDirectory() as raw:
    root = Path(raw)
    cnf = root / "parent.cnf"
    cnf.write_text("p cnf 20000 2\n18349 18350 18351 0\n1 0\n")
    manifest = root / "parent.manifest.json"
    manifest.write_text(json.dumps({
        "scope": "toy symbolic scope", "sha256": sha(cnf),
        "vars": 20000, "clauses": 2,
        "options": {"phase_symmetry": True},
    }))
    output = root / "cubes"
    splitter = Path(__file__).with_name("split_symbolic_phase_anchor.py")
    subprocess.run([sys.executable, str(splitter), str(manifest), str(cnf),
                    str(output)], check=True, capture_output=True, text=True)
    cubes = sorted(output.glob("*.cnf"))
    assert len(cubes) == 3
    for phase, cube in enumerate(cubes):
        lines = cube.read_text().splitlines()
        assert lines[0] == "p cnf 20000 3"
        assert lines[1:3] == ["18349 18350 18351 0", "1 0"]
        assert lines[3] == f"{18349 + phase} 0"
        doc = json.loads(cube.with_suffix(".manifest.json").read_text())
        assert doc["sha256"] == sha(cube)
        assert doc["cube_phase"] == phase
        assert doc["exhaustive_anchor_literals"] == [18349, 18350, 18351]

print("SYMBOLIC PHASE CUBE SPLITTER ALL OK")
