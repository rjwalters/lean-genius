#!/usr/bin/env python3
"""Bounded work queue for the v2 ledger-arm sweep (post-A/B requeue).
Usage: queue_v2.py <reps.jsonl> <outdir> [K=14] [arm=v2] [budget=900]
Resumable: skips jobs with an existing {tag}.verdict (old encoder run)
OR {tag}.{arm}.verdict (this run)."""
import json, subprocess, sys, os, hashlib, time
reps_path, outdir = sys.argv[1], sys.argv[2]
K = int(sys.argv[3]) if len(sys.argv) > 3 else 14
arm = sys.argv[4] if len(sys.argv) > 4 else "v2"
budget = sys.argv[5] if len(sys.argv) > 5 else "900"
os.makedirs(outdir, exist_ok=True)
jobs = [l.strip() for l in open(reps_path) if l.strip()]
def tag_of(line):
    mtab = {tuple(map(int, k.strip("()").split(","))): v
            for k, v in json.loads(line).items()}
    return hashlib.sha1(json.dumps(sorted(mtab.items())).encode()).hexdigest()[:16]
def done(j):
    t = tag_of(j)
    return (os.path.exists(f"{outdir}/{t}.verdict") or
            os.path.exists(f"{outdir}/{t}.{arm}.verdict"))
pending = [j for j in jobs if not done(j)]
print(f"{len(jobs)} jobs, {len(pending)} pending (arm={arm})", flush=True)
running = []
while pending or running:
    running = [p for p in running if p.poll() is None]
    while pending and len(running) < K:
        line = pending.pop(0)
        p = subprocess.Popen(["python3", "sweep_worker.py", line, outdir,
                              arm, budget],
                             stdout=open(f"{outdir}/queue.log", "a"),
                             stderr=subprocess.STDOUT)
        running.append(p)
    time.sleep(5)
print("QUEUE DONE", flush=True)
