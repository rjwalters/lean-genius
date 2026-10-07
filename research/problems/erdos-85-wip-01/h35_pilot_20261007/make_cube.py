#!/usr/bin/env python3
"""Write cube CNF = base + unit clauses of the cube (sorted by variable, inserted after header) via cube_verdict.cube_bytes."""
import sys, json
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "phase_b_h1_verdict_cloud_20260921"))
import cube_verdict
base, out, lits = Path(sys.argv[1]), Path(sys.argv[2]), json.loads(sys.argv[3])
raw, hi, nv, nc = cube_verdict.read_cnf(base)
out.write_bytes(cube_verdict.cube_bytes(raw, hi, nv, nc, {abs(l): int(l > 0) for l in lits}))
