#!/usr/bin/env python3
"""Small end-to-end test for the exhaustive phase-anchor cube splitter."""

import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

from verify_symbolic_hlift_assignment import phase_variable_map


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
        "encoder_sha256": "e" * 64,
        "sat_verifier_sha256": "v" * 64,
        "rule_counts": {"toy": 5},
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
        assert doc["rule_counts"] == {"toy": 5, "phase_anchor_cube_unit": 1}
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

    nested = root / "nested"
    nested.mkdir()
    mapping, _ = phase_variable_map()
    literals = [mapping[((1, 0), 2, phase)] for phase in range(3)]
    nested_cnf = nested / "p1.cnf"
    nested_cnf.write_text(
        f"p cnf 20000 4\n{' '.join(map(str, literals))} 0\n" +
        "".join(f"-{left} -{right} 0\n" for left, right in
                ((literals[0], literals[1]), (literals[0], literals[2]),
                 (literals[1], literals[2])))
    )
    nested_manifest = nested / "p1.manifest.json"
    nested_manifest.write_text(json.dumps({
        "scope": "toy parent AND tau[(0,0),2]=1",
        "sha256": sha(nested_cnf), "vars": 20000, "clauses": 4,
        "encoder_sha256": "e" * 64, "sat_verifier_sha256": "v" * 64,
        "rule_counts": {"toy": 3, "phase_anchor_cube_unit": 1},
        "options": {"phase_symmetry": True},
        "cube_phase": 1, "cube_literal": 18350,
        "exhaustive_anchor_literals": [18349, 18350, 18351],
    }))
    nested_output = nested / "children"
    subprocess.run([
        sys.executable, str(splitter), str(nested_manifest), str(nested_cnf),
        str(nested_output), "--anchor", "1", "0", "2",
    ], check=True, capture_output=True, text=True)
    children = sorted(nested_output.glob("*.manifest.json"))
    assert len(children) == 3
    for phase, child_path in enumerate(children):
        child = json.loads(child_path.read_text())
        assert child["cube_anchor"] == "tau[(1,0),2]"
        assert len(child["cube_ancestry"]) == 2
        assert child["cube_ancestry"][-1]["phase"] == phase
        assert child["rule_counts"]["phase_anchor_cube_unit_2"] == 1

print("SYMBOLIC PHASE CUBE SPLITTER ALL OK")
