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
    cnf.write_text(
        "p cnf 20000 5\n"
        "18349 18350 18351 0\n"
        "-18349 -18350 0\n"
        "-18349 -18351 0\n"
        "-18350 -18351 0\n"
        "1 0\n"
    )
    manifest = root / "parent.manifest.json"
    manifest.write_text(json.dumps({
        "scope": "toy symbolic scope", "sha256": sha(cnf),
        "vars": 20000, "clauses": 5,
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
        assert lines[0] == "p cnf 20000 6"
        assert lines[1:6] == [
            "18349 18350 18351 0",
            "-18349 -18350 0",
            "-18349 -18351 0",
            "-18350 -18351 0",
            "1 0",
        ]
        assert lines[6] == f"{18349 + phase} 0"
        doc = json.loads(cube.with_suffix(".manifest.json").read_text())
        assert doc["sha256"] == sha(cube)
        assert doc["cube_phase"] == phase
        assert doc["exhaustive_anchor_literals"] == [18349, 18350, 18351]
        assert doc["cube_partition_verified"] is True

    bad_cnf = root / "missing-exclusion.cnf"
    bad_cnf.write_text(
        cnf.read_text()
        .replace("p cnf 20000 5\n", "p cnf 20000 4\n")
        .replace("-18349 -18350 0\n", "")
    )
    bad_manifest = root / "missing-exclusion.manifest.json"
    bad_manifest.write_text(json.dumps({
        "scope": "bad toy symbolic scope", "sha256": sha(bad_cnf),
        "vars": 20000, "clauses": 4,
        "options": {"phase_symmetry": True},
    }))
    rejected = subprocess.run(
        [sys.executable, str(splitter), str(bad_manifest), str(bad_cnf),
         str(root / "bad-cubes"), "--dry-run"],
        capture_output=True, text=True,
    )
    assert rejected.returncode != 0
    assert "pairwise anchor exclusion" in rejected.stderr

print("SYMBOLIC PHASE CUBE SPLITTER ALL OK")
