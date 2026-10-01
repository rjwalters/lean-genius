#!/usr/bin/env python3
"""Goal #48: compiled Std LRAT.check (lratreplay, pinned image a5ca6c4e) of every solved pilot leaf.

Same checker and image as replay_historical96.py. Reads leaves/receipts.jsonl (UNSAT rows only),
checks cube.cnf sha256 against the receipt, runs lratreplay on cube.cnf + proof.lrat, and appends
one row per leaf to leaves/check-receipts.jsonl (as_completed; already-checked leaves skipped).
"""
import concurrent.futures as cf, hashlib, json, os, subprocess, sys, time
from pathlib import Path
OUT = Path(sys.argv[1])
WORKERS = int(os.environ.get("WORKERS", "1"))
TOOLS = "/Volumes/Stripe/lean-genius/artifacts/erdos85-conflict-v6-bootstrap-sol1-20260909.noindex/materialization-check/tools"
IMAGE = "sha256:a5ca6c4e3328a1832d5f9b814ab7c1e35616903b3956341962a5b1a96fb6dff6"

def sha(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for b in iter(lambda: f.read(1 << 22), b""): h.update(b)
    return h.hexdigest()

solved = [json.loads(l) for l in (OUT / "receipts.jsonl").read_text().splitlines() if l.strip()]
solved = [r for r in solved if r.get("verdict") == "UNSAT"]
chk_path = OUT / "check-receipts.jsonl"
done = {json.loads(l)["node"] for l in chk_path.read_text().splitlines() if l.strip()} if chk_path.exists() else set()

def run(r):
    d = OUT / f"node-{r['node']:05d}"
    rec = {"node": r["node"], "cube_sha256": r["cube_sha256"], "lrat_bytes": (d / "proof.lrat").stat().st_size}
    if sha(d / "cube.cnf") != r["cube_sha256"]:
        rec["status"] = "CUBE_SHA_MISMATCH"; return rec
    rec["lrat_sha256"] = sha(d / "proof.lrat")
    t0 = time.time()
    with open(d / "lratcheck.log", "wb") as f:
        rc = subprocess.run(["docker", "run", "--rm", "--network", "none", "--memory", "24g",
                             "-v", f"{TOOLS}:/tools:ro", "-v", f"{d}:/w:ro", IMAGE,
                             "/tools/bin/lratreplay", "/w/cube.cnf", "/w/proof.lrat"],
                            stdout=f, stderr=subprocess.STDOUT).returncode
    log = (d / "lratcheck.log").read_text(errors="replace")
    rec.update(lratreplay_rc=rc, lratreplay_wall=time.time() - t0,
               status="LRAT_CHECK_ACCEPTED" if rc == 0 and "LRAT accepted: true" in log else "LRAT_CHECK_FAILED",
               image=IMAGE, finished_utc=time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()))
    return rec

todo = sorted((r for r in solved if r["node"] not in done), key=lambda r: r["lrat_bytes"])
print(f"{len(todo)} leaves to check, {WORKERS} workers", flush=True)
with cf.ThreadPoolExecutor(WORKERS) as ex, open(chk_path, "a") as out:
    for fut in cf.as_completed([ex.submit(run, r) for r in todo]):
        rec = fut.result(); out.write(json.dumps(rec) + "\n"); out.flush()
        print("CHECK", rec["node"], rec["status"], round(rec.get("lratreplay_wall", 0)), rec["lrat_bytes"], flush=True)
