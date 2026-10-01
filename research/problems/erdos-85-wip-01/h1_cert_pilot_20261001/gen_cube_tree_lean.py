#!/usr/bin/env python3
"""Emit the Lean CubeTree term + solver-side cube list for a banked adaptive cube tree."""
import json, sys
from pathlib import Path
res = json.loads(Path(sys.argv[1]).read_text()); name = sys.argv[2]
N = res["nodes"]
def term(i, ind):
    n = N[str(i)]
    if n["kind"] == "leaf":
        assert n["status"] == "UNSAT_CROSSCHECKED", n["id"]
        return ".leaf"
    v = n["split_variable"]; p, q = n["children"]
    assert N[str(p)]["literals"] == n["literals"] + [v] and N[str(q)]["literals"] == n["literals"] + [-v]
    pad = " " * (ind + 2)
    return f"(.split {v - 1}\n{pad}{term(p, ind + 2)}\n{pad}{term(q, ind + 2)})"
leaves = sorted((n for n in N.values() if n["kind"] == "leaf"), key=lambda n: n["id"])
cubes = [sorted(n["literals"], key=abs) for n in leaves]
print(f"/-- Banked adaptive cube tree of `{res['case_id']}` (base sha256 {res['base_sha256']}). -/")
print(f"def {name}Tree : CubeTree :=\n  {term(0, 2)}\n")
print(f"/-- Solver-side leaf cubes (node ids {[n['id'] for n in leaves]}), literals sorted by variable as in `cube_bytes`. -/")
print(f"def {name}Cubes : List (List Int) := [\n" + ",\n".join("  " + json.dumps(c) for c in cubes) + "]")
