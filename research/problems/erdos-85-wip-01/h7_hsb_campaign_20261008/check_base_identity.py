#!/usr/bin/env python3
"""Base-cube byte identity: Lean term `orderFortyNineSevenHighT0CanonicalEmptyCubeSatCnf F i`
(printed by EmitCube.lean, read from stdin as concatenated DIMACS files) against the frozen root
hashes of the reviewed Python generator (h7-frontier-map-20260915/results.json), which are the
`cube_cnf_sha256` values pinned in the campaign inputs.json.

Run inside the pinned Lean image from proofs/ (see check_base_identity.sh).
"""
from __future__ import annotations

import hashlib
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import h7_common as hc  # noqa: E402

roots = {r["id"]: r for r in json.loads((HERE.parent / "h7-frontier-map-20260915/results.json").read_text())["rows"]}
out_path = Path(sys.argv[1]) if len(sys.argv) > 1 else None
segments: list[dict] = []
h = None
for line in sys.stdin.buffer:
    if line.startswith(b"p cnf "):
        if h is not None:
            segments[-1]["sha256"] = h.hexdigest()
        h = hashlib.sha256()
        segments.append({"header": line.decode().strip(), "clauses": 0, "bytes": 0})
    else:
        segments[-1]["clauses"] += 1
    h.update(line)
    segments[-1]["bytes"] += len(line)
if h is not None:
    segments[-1]["sha256"] = h.hexdigest()
ok = len(segments) == len(hc.CUBES)
results = []
for name, seg in zip(hc.CUBES, segments):
    want = roots[name]["cnf_sha256"]
    good = (seg["sha256"] == want and seg["header"] == f"p cnf {hc.VARIABLES} {hc.CUBE_CLAUSES}"
            and seg["clauses"] == hc.CUBE_CLAUSES)
    ok = ok and good
    rec = {"root": name, "mask": roots[name]["mask"], "lean_cube_cnf_sha256": seg["sha256"],
           "python_frozen_cnf_sha256": want, "bytes": seg["bytes"], "clauses": seg["clauses"], "identical": good}
    results.append(rec)
    print(json.dumps(rec, sort_keys=True), flush=True)
summary = {"schema": "erdos85-h7-base-cube-lean-identity-v1", "all_ok": ok, "count": len(segments),
           "lean_term": "orderFortyNineSevenHighT0CanonicalEmptyCubeSatCnf F i", "results": results}
if out_path:
    out_path.write_text(json.dumps(summary, indent=1, sort_keys=True) + "\n")
print("BASE_IDENTITY_ALL_OK" if ok else "BASE_IDENTITY_MISMATCH", flush=True)
sys.exit(0 if ok else 1)
