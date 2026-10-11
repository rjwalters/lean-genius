#!/usr/bin/env python3
"""Campaign-wide totals over every H7 result file (main, residual and split passes), by kind and status.

    campaign_totals.py RESULTS_DIR > receipts/collected/campaign_totals.json

`collect_receipts.py` totals count only the receipts that certify a leaf or split item (no covers,
no superseded runs); this script counts every run record, including the 28 covers and the runs that
hit a solver cap and were re-run.
"""
import collections, glob, json, subprocess, sys

def main(d):
    keys = collections.defaultdict(lambda: {"runs": 0, "solver_cpu_hours": 0.0, "checker_cpu_hours": 0.0, "proof_bytes": 0})
    files = sorted(glob.glob(d + "/*.jsonl.zst"))
    for f in files:
        out = subprocess.run(["zstd", "-dcq", f], capture_output=True, check=True).stdout.decode()
        for line in out.splitlines():
            if not line.strip():
                continue
            r = json.loads(line)
            kind = r.get("kind")
            k = "cover" if kind == "cover" else "split" if kind in ("subleaf", "subcover") else "leaf"
            e = keys[f"{k}:{r.get('status')}"]
            e["runs"] += 1
            e["solver_cpu_hours"] += ((r.get("solver") or {}).get("cpu_seconds") or 0) / 3600
            e["checker_cpu_hours"] += ((r.get("checker") or {}).get("cpu_seconds") or 0) / 3600
            e["proof_bytes"] += (r.get("proof") or {}).get("bytes") or 0
    rows = {k: {**v, "solver_cpu_hours": round(v["solver_cpu_hours"], 2), "checker_cpu_hours": round(v["checker_cpu_hours"], 2)}
            for k, v in sorted(keys.items())}
    tot = {f: (round(sum(v[f] for v in keys.values()), 2) if f != "runs" and f != "proof_bytes" else sum(v[f] for v in keys.values()))
           for f in ("runs", "solver_cpu_hours", "checker_cpu_hours", "proof_bytes")}
    print(json.dumps({"schema": "erdos85-h7-campaign-totals-v1", "result_files": len(files), "by_kind_status": rows, "all_runs": tot}, indent=1, sort_keys=True))

if __name__ == "__main__":
    main(sys.argv[1])
