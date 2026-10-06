#!/usr/bin/env python3
"""Check the hardest H1 orbit (h1_81494a6ef36d3ec9) through its banked cube tree.

Regenerate the base CNF with the pinned v2cnf and require sha256 == the tree's base_sha256; for each of
the 36 leaves rebuild the cube CNF (base + the leaf's unit literals, via the census's own
phase_b_h1_verdict_cloud_20260921/cube_verdict.cube_bytes) and require its sha256 == the banked
cube_sha256; then solve it with CaDiCaL (binary LRAT) streamed into cake_lpr (cert_row.solve_and_check).
That the 36 leaves cover the base formula is proved in Lean (cnf_unsat_of_h1Cube81494a; the tree and
the cover are Lean terms checked by kernel decide; axioms propext, Quot.sound).
"""
import argparse, hashlib, importlib.util, json, sys, subprocess
from pathlib import Path
HERE = Path(__file__).resolve().parent
W = HERE.parent
sys.path.insert(0, str(W / "phase_b_h1_verdict_cloud_20260921"))
import cube_verdict  # noqa: E402
spec = importlib.util.spec_from_file_location("cert_row", W / "h1_cert_full_20261001" / "cert_row.py")
cert_row = importlib.util.module_from_spec(spec); spec.loader.exec_module(cert_row)


def sha(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for b in iter(lambda: f.read(1 << 22), b""):
            h.update(b)
    return h.hexdigest()


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--kit", type=Path, required=True); p.add_argument("--out", type=Path, required=True)
    p.add_argument("--v2cnf", required=True); p.add_argument("--cadical", required=True); p.add_argument("--cake-lpr", required=True)
    p.add_argument("--heap-mb", type=int, default=8000); p.add_argument("--leaves", default="", help="comma-separated node ids (default: all)")
    a = p.parse_args()
    meta = json.loads((a.kit / "cube" / "h1_81494a6ef36d3ec9.meta.json").read_text())
    tree = json.loads((a.kit / "cube" / "h1_81494a6ef36d3ec9.results.json").read_text())
    out = a.out.resolve(); out.mkdir(parents=True, exist_ok=True)
    base_dir = out / "base"; base_dir.mkdir(exist_ok=True)
    ns = argparse.Namespace(table=a.kit / "tables" / "h1_81494a6ef36d3ec9.json", profile=meta["profile"], cnf_sha256=meta["base_sha256"],
                            v2cnf=Path(a.v2cnf), image=cert_row.__dict__.get("IMAGE", "sha256:a5ca6c4e3328a1832d5f9b814ab7c1e35616903b3956341962a5b1a96fb6dff6"),
                            docker="docker", cadical=a.cadical, cake_lpr=a.cake_lpr, cap=172800, heap_mb=a.heap_mb)
    ns.image = "sha256:a5ca6c4e3328a1832d5f9b814ab7c1e35616903b3956341962a5b1a96fb6dff6"
    rec = {}
    base = cert_row.emit_cnf(ns, base_dir, rec)
    summary = {"base_sha256_match": base is not None, "leaves": {}}
    if base is None:
        print(json.dumps(summary)); sys.exit(1)
    raw, header_index, variables, clauses = cube_verdict.read_cnf(base)
    want = set(a.leaves.split(",")) if a.leaves else None
    for n in sorted((n for n in tree["nodes"].values() if n["kind"] == "leaf"), key=lambda n: n["id"]):
        if want and str(n["id"]) not in want:
            continue
        d = out / f"leaf-{n['id']:05d}"; d.mkdir(exist_ok=True)
        cnf = d / "cube.cnf"
        cnf.write_bytes(cube_verdict.cube_bytes(raw, header_index, variables, clauses, {abs(l): int(l > 0) for l in n["literals"]}))
        r = {"cube_sha256_match": sha(cnf) == n["cube_sha256"]}
        if r["cube_sha256_match"]:
            cert_row.solve_and_check(ns, d, cnf, r)
        else:
            r["status"] = "CUBE_MISMATCH"
        cnf.unlink(missing_ok=True)
        (d / "receipt.json").write_text(json.dumps(r, indent=1) + "\n")
        summary["leaves"][n["id"]] = r["status"]
        print(n["id"], r["status"], flush=True)
    ok = summary["base_sha256_match"] and all(s == "CERTIFIED" for s in summary["leaves"].values())
    summary["all_leaves_certified"] = ok and len(summary["leaves"]) == meta["leaves"]
    (out / "SUMMARY.json").write_text(json.dumps(summary, indent=1) + "\n")
    print(json.dumps({k: v for k, v in summary.items() if k != "leaves"}))


if __name__ == "__main__":
    main()
