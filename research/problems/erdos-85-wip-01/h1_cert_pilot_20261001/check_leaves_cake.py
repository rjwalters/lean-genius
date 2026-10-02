#!/usr/bin/env python3
"""Goal #48: check every solved pilot leaf with cake_lpr (CakeML-verified LRAT/LPR checker).

Streaming checker with a bounded heap (HEAP_MB, default 4000), so memory does not scale with
proof size the way the in-memory Std LRAT.check does (~10x proof bytes). Binary LRAT is read
natively. Sequential by default; receipts -> leaves/cake-check-receipts.jsonl (as_completed).
"""
import concurrent.futures as cf, hashlib, json, os, subprocess, sys, time
from pathlib import Path
OUT = Path(sys.argv[1])
CAKE = os.environ.get("CAKE_LPR", "/Volumes/Stripe/lean-genius/cake_lpr-src/cake_lpr")
HEAP = os.environ.get("HEAP_MB", "4000")
WORKERS = int(os.environ.get("WORKERS", "1"))

def sha(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for b in iter(lambda: f.read(1 << 22), b""): h.update(b)
    return h.hexdigest()

CAKE_SHA = sha(CAKE)
solved = [json.loads(l) for l in (OUT / "receipts.jsonl").read_text().splitlines() if l.strip()]
solved = [r for r in solved if r.get("verdict") == "UNSAT"]
path = OUT / "cake-check-receipts.jsonl"
done = {json.loads(l)["node"] for l in path.read_text().splitlines() if l.strip()} if path.exists() else set()

def run(r):
    d = OUT / f"node-{r['node']:05d}"
    rec = {"node": r["node"], "cube_sha256": r["cube_sha256"], "lrat_bytes": (d / "proof.lrat").stat().st_size,
           "checker": "cake_lpr", "checker_sha256": CAKE_SHA, "heap_mb": int(HEAP)}
    if sha(d / "cube.cnf") != r["cube_sha256"]:
        rec["status"] = "CUBE_SHA_MISMATCH"; return rec
    t0 = time.time()
    with open(d / "cake_lpr.log", "wb") as f:
        p = subprocess.Popen([CAKE, str(d / "cube.cnf"), str(d / "proof.lrat"), f"--CML_HEAP_SIZE={HEAP}", "--CML_STACK_SIZE=1000"],
                             stdout=f, stderr=subprocess.STDOUT)
        _, st, ru = os.wait4(p.pid, 0)
    log = (d / "cake_lpr.log").read_text(errors="replace")
    rc = os.waitstatus_to_exitcode(st)
    rec.update(returncode=rc, wall_seconds=time.time() - t0, cpu_seconds=ru.ru_utime + ru.ru_stime, maxrss_bytes=ru.ru_maxrss,
               status="CAKE_LPR_VERIFIED" if rc == 0 and "s VERIFIED UNSAT" in log else "CAKE_LPR_FAILED",
               finished_utc=time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()))
    return rec

todo = sorted((r for r in solved if r["node"] not in done), key=lambda r: r["lrat_bytes"])
print(f"{len(todo)} leaves, cake_lpr {CAKE_SHA[:12]}, heap {HEAP} MB, {WORKERS} workers", flush=True)
with cf.ThreadPoolExecutor(WORKERS) as ex, open(path, "a") as out:
    for fut in cf.as_completed([ex.submit(run, r) for r in todo]):
        rec = fut.result(); out.write(json.dumps(rec) + "\n"); out.flush()
        print("CAKE", rec["node"], rec["status"], round(rec.get("wall_seconds", 0)), round(rec.get("maxrss_bytes", 0) / 1e9, 2), rec["lrat_bytes"], flush=True)
