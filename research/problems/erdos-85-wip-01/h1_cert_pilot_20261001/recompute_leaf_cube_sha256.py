#!/usr/bin/env python3
"""Recompute the cube-CNF sha256 of all 36 leaves of pilot root h1_81494a6ef36d3ec9 (review jhpvtq).

Base CNF = h1-cube-pass4-20260926/h1_81494a6ef36d3ec9/run-adaptive/base.cnf (sha256 must equal the banked
tree base_sha256 860d8af2...177d = census cnf_sha256). Each leaf CNF = cube_verdict.cube_bytes(base, leaf unit
literals) -- the same function solve_leaves.py and h1_checker_kit/cube_check.py use. Output (stdout): the TSV
h1_cert_full_20261001/receipts/pilot_h1_81494a_leaf_expected_sha256.tsv. Read-only; touches no receipt.
"""
import hashlib, json, sys
from pathlib import Path
W = Path("/Volumes/Stripe/lean-genius/erdos85-review-deposit/research/problems/erdos-85-wip-01")
sys.path.insert(0, str(W / "phase_b_h1_verdict_cloud_20260921")); sys.path.insert(0, str(W / "sat49"))
import cube_verdict
CASE = Path("/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/h1-cube-pass4-20260926/h1_81494a6ef36d3ec9")
PILOT = Path("/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/h1-cert-pilot-20261001/leaves")
sha = lambda b: hashlib.sha256(b).hexdigest()
def fsha(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for b in iter(lambda: f.read(1 << 22), b""): h.update(b)
    return h.hexdigest()
banked = json.loads((W / "phase_b_h1_census_20260927/cube-h1_81494a6ef36d3ec9/results.json").read_text())
stripe = json.loads((CASE / "run-adaptive/results.json").read_text())
print("banked tree == stripe tree:", banked["nodes"] == stripe["nodes"], banked["base_sha256"], file=sys.stderr)
basep = CASE / "run-adaptive/base.cnf"
bs = fsha(basep); assert bs == banked["base_sha256"], bs
base = cube_verdict.read_cnf(basep)
rec = {json.loads(l)["node"]: json.loads(l) for l in (W / "h1_cert_full_20261001/receipts/pilot_h1_81494a_leaf_solves.jsonl").read_text().splitlines() if l.strip()}
leaves = sorted((n for n in banked["nodes"].values() if n["kind"] == "leaf"), key=lambda n: n["id"])
assert len(leaves) == 36 and set(rec) == {n["id"] for n in leaves}
print("node\tliterals\texpected_cube_sha256\treceipt_cube_sha256\trecomputed_cube_sha256\tondisk_cube_sha256\treceipt_had_cube_sha_ok\tmatch")
bad = 0
for n in leaves:
    i = n["id"]; r = rec[i]
    assert r["literals"] == n["literals"]
    got = sha(cube_verdict.cube_bytes(*base, {abs(l): int(l > 0) for l in n["literals"]}))
    disk = fsha(PILOT / f"node-{i:05d}/cube.cnf") if (PILOT / f"node-{i:05d}/cube.cnf").exists() else "-"
    ok = got == n["cube_sha256"] == r["cube_sha256"] and disk in (got, "-")
    bad += not ok
    print(f"{i}\t{' '.join(map(str, n['literals']))}\t{n['cube_sha256']}\t{r['cube_sha256']}\t{got}\t{disk}\t{'cube_sha_ok' in r}\t{'MATCH' if ok else 'MISMATCH'}")
print("mismatches:", bad, file=sys.stderr)
