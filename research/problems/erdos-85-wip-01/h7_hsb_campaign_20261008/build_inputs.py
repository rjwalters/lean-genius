#!/usr/bin/env python3
"""Build the pinned campaign inputs for the 28 structural H7/T0 cubes.

    build_inputs.py --h7hsb <native h7hsb> --out <dir> [--jobs 6] [--leaf-manifest]

* canonical.body + <cube>.units come from the reviewed compact Python generator; every cube CNF
  must hash to the frozen root hash in h7-frontier-map-20260915/results.json.
* <cube>.hsb / <cube>.cover are the stdout of the native Lean emitter `h7hsb` (the compiled print
  of `SevenHighT0Hsb.clauses 3 mask` / `coverClauses 3 mask`); their sha256 must equal the
  Lean values in ../h7_structural_pilot_20261008/receipts/hsb_lean_identity.json.
* inputs.json pins everything, including sha256 of the cube / hsb / cover CNFs and of the
  per-cube leaf manifest (one line per leaf: index, units, leaf CNF sha256).
* --leaf-manifest also writes <cube>.leaves.jsonl (377,776 lines in total, ~80 MB).

Deterministic: the same h7hsb binary and repository commit give the same inputs.json.
"""
from __future__ import annotations

import argparse
import concurrent.futures as cf
import hashlib
import json
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
PILOT = HERE.parent / "h7_structural_pilot_20261008"
sys.path.insert(0, str(PILOT))
sys.path.insert(0, str(HERE))
import gen_pilot as gp  # noqa: E402
import h7_common as hc  # noqa: E402


def run_h7hsb(exe: str, mode: str, mask: int, out: Path) -> str:
    with open(out, "wb") as f:
        r = subprocess.run([exe, mode, str(hc.DEPTH), str(mask)], stdout=f, stderr=subprocess.PIPE, text=False)
    if r.returncode != 0:
        raise RuntimeError(f"h7hsb {mode} {mask}: rc={r.returncode} {r.stderr[-300:]!r}")
    return r.stderr.decode().strip()


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--h7hsb", required=True)
    ap.add_argument("--out", type=Path, required=True)
    ap.add_argument("--jobs", type=int, default=6)
    ap.add_argument("--leaf-manifest", action="store_true")
    args = ap.parse_args()
    out = args.out
    out.mkdir(parents=True, exist_ok=True)
    t0 = time.time()
    roots = gp.roots()
    identity = {r["root"]: r for r in json.loads((PILOT / "receipts/hsb_lean_identity.json").read_text())["results"]}
    cnf, edge_vars, _ = gp.canonical.build_cnf(gp.compact.CompactCnf)
    assert cnf.variable_count == hc.VARIABLES and len(cnf.clauses) == hc.CANONICAL_CLAUSES
    body = "".join(" ".join(map(str, c)) + " 0\n" for c in cnf.clauses).encode()
    (out / "canonical.body").write_bytes(body)
    meta = {"schema": "erdos85-h7-hsb-inputs-v1", "depth": hc.DEPTH, "variables": hc.VARIABLES,
            "canonical_clauses": hc.CANONICAL_CLAUSES, "canonical_body_sha256": hc.sha_bytes(body),
            "h7hsb_sha256": hc.sha_file(Path(args.h7hsb)), "cubes": {}}
    for name in hc.CUBES:
        mask = roots[name]["mask"]
        units = []
        for index, (l, r) in enumerate(gp.quotient.EDGES):
            v = edge_vars[(7 + l, 7 + r)]
            units.append(v if (mask >> index) & 1 else -v)
        ub = "".join(f"{u} 0\n" for u in units).encode()
        (out / f"{name}.units").write_bytes(ub)
        digest = hc.sha_bytes(hc.header(hc.CUBE_CLAUSES) + body + ub)
        assert digest == roots[name]["cnf_sha256"], (name, digest)
        meta["cubes"][name] = {"mask": mask, "edge_count": roots[name]["edge_count"], "cube_cnf_sha256": digest,
                               "units_sha256": hc.sha_bytes(ub)}
    print(f"base cubes ok ({time.time() - t0:.0f}s)", flush=True)

    def emit(name: str) -> str:
        mask = meta["cubes"][name]["mask"]
        err = run_h7hsb(args.h7hsb, "hsb", mask, out / f"{name}.hsb")
        err2 = run_h7hsb(args.h7hsb, "cover", mask, out / f"{name}.cover")
        return f"{name}: {err} {err2}"

    with cf.ThreadPoolExecutor(args.jobs) as ex:
        for line in ex.map(emit, hc.CUBES):
            print(line, flush=True)
    total_leaves = total_hsb = 0
    for name in hc.CUBES:
        m = meta["cubes"][name]
        hsb = (out / f"{name}.hsb").read_bytes()
        cover = (out / f"{name}.cover").read_bytes()
        ub = (out / f"{name}.units").read_bytes()
        ident = identity[name]
        m["hsb_sha256"], m["cover_sha256"] = hc.sha_bytes(hsb), hc.sha_bytes(cover)
        assert ident["ok"] and ident["mask"] == m["mask"], name
        assert m["hsb_sha256"] == ident["lean_hsb_sha256"] == ident["python_hsb_sha256"], name
        assert m["cover_sha256"] == ident["lean_cover_sha256"] == ident["python_cover_sha256"], name
        m["hsb_clauses"], m["leaves"] = hsb.count(b"\n"), cover.count(b"\n")
        assert m["hsb_clauses"] == ident["hsb_clauses"] and m["leaves"] == ident["leaves"], name
        lines = cover.splitlines()
        m["leaf_units"] = len(hc.units_of_cover_line(lines[0]))
        m["hsb_cnf_sha256"] = hc.sha_bytes(hc.header(hc.CUBE_CLAUSES + m["hsb_clauses"]) + body + ub + hsb)
        m["cover_cnf_sha256"] = hc.sha_bytes(
            hc.header(hc.CUBE_CLAUSES + m["hsb_clauses"] + m["leaves"]) + body + ub + hsb + cover)
        m["leaf_cnf_clauses"] = hc.CUBE_CLAUSES + m["hsb_clauses"] + m["leaf_units"]
        m["leaf_cnf_bytes"] = len(hc.header(m["leaf_cnf_clauses"])) + len(body) + len(ub) + len(hsb)  # + units
        total_leaves += m["leaves"]
        total_hsb += m["hsb_clauses"]
    meta["total_leaves"], meta["total_hsb_clauses"] = total_leaves, total_hsb
    (out / "inputs.json").write_text(json.dumps(meta, indent=1, sort_keys=True) + "\n")
    # Leaf manifests: needs inputs.json on disk (Cube reads it), then pins their hashes.
    for name in hc.CUBES:
        cube = hc.Cube(out, name)
        h = hashlib.sha256()
        fh = open(out / f"{name}.leaves.jsonl", "wb") if args.leaf_manifest else None
        for n in range(cube.n_leaves):
            line = (json.dumps({"cube": name, "leaf": n, "units": cube.units(n), "cnf_sha256": cube.leaf_sha256(n)},
                               sort_keys=True) + "\n").encode()
            h.update(line)
            if fh:
                fh.write(line)
        if fh:
            fh.close()
        meta["cubes"][name]["leaf_manifest_sha256"] = h.hexdigest()
    meta["batch"] = hc.BATCH
    meta["batches"] = len(hc.batches(meta))
    meta["batch_manifest_sha256"] = hc.sha_bytes(hc.manifest_bytes(meta))
    (out / "inputs.json").write_text(json.dumps(meta, indent=1, sort_keys=True) + "\n")
    print(json.dumps({"total_leaves": total_leaves, "total_hsb_clauses": total_hsb, "batches": meta["batches"],
                      "inputs_json_sha256": hc.sha_file(out / "inputs.json"), "seconds": round(time.time() - t0)}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
