#!/usr/bin/env python3
"""Backfill leaves/receipts.jsonl for leaves that finished before the 2026-10-01 host crash.

The original driver wrote receipts in submission order (ex.map), so the 31 finished leaves had
no receipt when the host went down. Each receipt here is rebuilt from that leaf's cadical.log
(exit code, process/real time, max RSS), cube.cnf sha256 and proof.lrat size, and is marked
"backfilled_from_log": true. Leaves without "c exit 20" are skipped (they must be re-solved).
"""
import hashlib, json, re, sys, time
from pathlib import Path
HERE = Path(__file__).resolve().parent
OUT = Path(sys.argv[1])
CASE = Path("/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/h1-cube-pass4-20260926/h1_81494a6ef36d3ec9")
nodes = {n["id"]: n for n in json.loads((CASE / "run-adaptive/results.json").read_text())["nodes"].values() if n["kind"] == "leaf"}
rec_path = OUT / "receipts.jsonl"
done = {json.loads(l)["node"] for l in rec_path.read_text().splitlines() if l.strip()} if rec_path.exists() else set()

def sha(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for b in iter(lambda: f.read(1 << 22), b""): h.update(b)
    return h.hexdigest()

def num(pat, log):
    m = re.search(pat, log); return float(m.group(1)) if m else None

with open(rec_path, "a") as rec:
    for i, n in sorted(nodes.items()):
        d = OUT / f"node-{i:05d}"
        if i in done or not (d / "cadical.log").exists(): continue
        log = (d / "cadical.log").read_text(errors="replace")
        if not re.search(r"^c exit 20$", log, re.M) or "s UNSATISFIABLE" not in log: continue
        csha = sha(d / "cube.cnf")
        r = {"node": i, "literals": n["literals"], "cube_sha256": csha, "cube_sha_ok": csha == n["cube_sha256"],
             "returncode": 20, "verdict": "UNSAT",
             "wall_seconds": num(r"total real time since initialization:\s+([\d.]+)", log),
             "cpu_seconds": num(r"total process time since initialization:\s+([\d.]+)", log),
             "maxrss_bytes": int(num(r"maximum resident set size of process:\s+([\d.]+)", log) * 2**20),
             "lrat_bytes": (d / "proof.lrat").stat().st_size, "lrat_binary": True,
             "prior_kissat_seconds": n["primary"]["elapsed_seconds"],
             "prior_cadical_seconds": n["crosscheck"]["elapsed_seconds"],
             "finished_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime((d / "cadical.log").stat().st_mtime)),
             "backfilled_from_log": True}
        rec.write(json.dumps(r) + "\n")
        print(i, r["verdict"], round(r["wall_seconds"]), r["lrat_bytes"], r["cube_sha_ok"])
