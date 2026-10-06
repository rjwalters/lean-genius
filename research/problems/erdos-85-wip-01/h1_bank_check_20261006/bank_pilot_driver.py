#!/usr/bin/env python3
"""Run bank_check_row.py over a tag list (as_completed, N workers); one JSON line per row to <out>/driver.jsonl."""
import concurrent.futures as cf, json, subprocess, sys, os
from pathlib import Path
tags_file, out, workers, heap = sys.argv[1], Path(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
row = Path(__file__).with_name("bank_check_row.py")
tags = [t for t in Path(tags_file).read_text().split() if not (out / t / "receipt.json").exists()]
def run(t):
    subprocess.run([sys.executable, str(row), t, "--out", str(out), "--heap-mb", heap], capture_output=True)
    p = out / t / "receipt.json"
    r = json.loads(p.read_text()) if p.exists() else {"tag": t, "status": "NO_RECEIPT"}
    return {k: r.get(k) for k in ("tag", "status", "wall_seconds", "gz_bytes", "lrat_bytes", "cnf_match", "gz_match", "lrat_match", "failure")}
with cf.ThreadPoolExecutor(workers) as ex, open(out / "driver.jsonl", "a") as log:
    for f in cf.as_completed([ex.submit(run, t) for t in tags]):
        r = f.result(); log.write(json.dumps(r) + "\n"); log.flush(); print(r["tag"], r["status"], flush=True)
