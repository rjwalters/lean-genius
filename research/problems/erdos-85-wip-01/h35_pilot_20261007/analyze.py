#!/usr/bin/env python3
"""Summarize pilot results.jsonl: per (cell, depth) solve-time distribution and Knuth estimates.

For depth d, a walk's weight W_d = prod of branching factors along its first d levels is an unbiased
estimate of the number of depth-d cubes (Knuth 1975), so
  leaves_hat(d) = mean_w W_d,   cpu_hat(d) = mean_w W_d * t_w(d)
estimates the frontier size and the total CaDiCaL time of solving the whole depth-d frontier.
A timed-out cube contributes t = cap, so cpu_hat is then a LOWER bound (marked '>=').
usage: analyze.py results.jsonl [spot_usd_per_vcpu_hour]
"""
import json, statistics as st, sys, collections
rows = [json.loads(l) for l in open(sys.argv[1])]
usd = float(sys.argv[2]) if len(sys.argv) > 2 else 0.94 / 64
B = [r for r in rows if r.get("phase") == "B"]
# walks per cell (phase A): a walk that ended (UP-refuted subtree) before depth d contributes W_d = 0
nwalks = collections.Counter()
for r in rows:
    if r.get("phase") == "A":
        for k in r["walks"]:
            nwalks[k.split("/")[0]] += 1
out = {}
groups = collections.defaultdict(list)
for r in B:
    groups[(r["cell"], r["depth"])].append(r)
print(f"{'cell':6} {'d':>3} {'n':>3} {'unsat':>5} {'unk':>4} {'med_s':>7} {'max_s':>7} {'leaves_hat':>11} {'cpu_h_hat':>12} {'usd_hat':>10}")
for (cell, d), g in sorted(groups.items()):
    ts = [r["wall_s"] for r in g]
    uns = sum(r["result"] == "UNSAT" for r in g); unk = sum(r["result"] == "UNKNOWN" for r in g)
    sat = sum(r["result"] == "SAT" for r in g)
    tried = max(nwalks.get(cell, 0), len(g))  # every walk of the cell is a sample; W_d = 0 if it ended early
    lh = sum(r["W"] for r in g) / tried
    cpu = sum(r["W"] * r["wall_s"] for r in g) / tried / 3600
    lb = ">=" if unk else "  "
    print(f"{cell:6} {d:>3} {len(g):>3} {uns:>5} {unk:>4} {st.median(ts):>7.0f} {max(ts):>7.0f} {lh:>11.3g} {lb}{cpu:>10.3g} {lb}{cpu * usd:>8.3g}" + (f"  SAT={sat}" if sat else ""))
    out[f"{cell}/d{d}"] = {"n": len(g), "unsat": uns, "unknown": unk, "sat": sat, "times_s": sorted(ts), "leaves_hat": lh,
                           "cpu_h_hat": cpu, "cpu_h_hat_is_lower_bound": bool(unk), "usd_hat": cpu * usd}
for r in rows:
    if r.get("phase") == "C":
        print("CERT", r["cell"], r["depth"], r.get("status"), r.get("proof", {}).get("bytes"),
              round(r.get("solver", {}).get("wall_seconds", 0)), round(r.get("checker", {}).get("wall_seconds", 0)))
json.dump(out, open(sys.argv[1].replace(".jsonl", ".summary.json"), "w"), indent=1)
