#!/usr/bin/env python3
"""Cost estimate for the H7 t=0 hsb3 campaign from the per-cube leaf sample (sample.py receipts).

    estimate.py --inputs-json inputs.json --sample results.jsonl [--json out.json] [--md out.md]

Per leaf the campaign cost is solver CPU + checker CPU (both measured by wait4 rusage on the exact
campaign path). Per cube: leaves x sample mean. Range: stratified bootstrap (resample within each
cube), 5%-95%. The bootstrap cannot see leaves harder than the sample maximum, so the tail is
reported separately (share of the estimate carried by the largest samples, capped leaves, a
Hill tail index on the pooled normalised sample, and a rule-of-three bound on capped leaves).
"""
from __future__ import annotations

import argparse
import json
import math
import random
import statistics as st
from pathlib import Path

SPOT_PER_VCPU_H = 0.0147
BUILDER_PER_VCPU_H = 0.8568 / 16
UTILISATION = 0.85  # solver+checker CPU delivered per paid vCPU-hour at slots = vCPUs (see README)
NODE_OVERHEAD_USD = 0.12  # controller's own 10% margin is on top of this


def pct(xs: list[float], q: float) -> float:
    xs = sorted(xs)
    return xs[min(len(xs) - 1, int(q * len(xs)))]


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--inputs-json", type=Path, required=True)
    ap.add_argument("--sample", type=Path, required=True)
    ap.add_argument("--json", type=Path)
    ap.add_argument("--md", type=Path)
    ap.add_argument("--boot", type=int, default=5000)
    a = ap.parse_args()
    meta = json.loads(a.inputs_json.read_text())
    recs = [json.loads(l) for l in a.sample.read_text().splitlines() if l.strip()]
    covers = [r for r in recs if r["kind"] == "cover"]
    by: dict[str, list[dict]] = {}
    for r in recs:
        if r["kind"] == "leaf":
            by.setdefault(r["cube"], []).append(r)
    rng = random.Random(1)
    rows, boots = [], [0.0] * a.boot
    pooled_norm, total = [], {"leaves": 0, "cpu_h": 0.0, "solver_h": 0.0, "checker_h": 0.0, "proof_bytes": 0.0, "n": 0,
                              "capped": 0, "not_certified": 0}
    for name, c in meta["cubes"].items():
        rs = by.get(name, [])
        if not rs:
            continue
        L, n = c["leaves"], len(rs)
        sol = [r.get("solver", {}).get("cpu_seconds", 0.0) for r in rs]
        chk = [r.get("checker", {}).get("cpu_seconds", 0.0) for r in rs]
        x = [s + k for s, k in zip(sol, chk)]
        pb = [r.get("proof", {}).get("bytes") or 0 for r in rs]
        capped = [r for r in rs if r["status"] == "SOLVER_TIMEOUT"]
        bad = [r for r in rs if r["status"] not in ("CERTIFIED", "SOLVER_TIMEOUT")]
        mean = st.mean(x)
        bs = []
        for b in range(a.boot):
            m = sum(x[rng.randrange(n)] for _ in range(n)) / n
            bs.append(m)
            boots[b] += L * m / 3600
        bs.sort()
        med = st.median(x)
        pooled_norm += [v / mean for v in x]
        row = {"cube": name, "leaves": L, "hsb_clauses": c["hsb_clauses"], "sampled": n, "certified": sum(r["status"] == "CERTIFIED" for r in rs),
               "capped": len(capped), "other": len(bad), "mean_s": mean, "median_s": med, "p90_s": pct(x, 0.9), "max_s": max(x),
               "mean_solver_s": st.mean(sol), "mean_checker_s": st.mean(chk),
               "mean_conflicts": st.mean([r.get("solver", {}).get("conflicts") or 0 for r in rs]),
               "mean_proof_mb": st.mean(pb) / 1e6, "cpu_h": L * mean / 3600, "cpu_h_lo": L * bs[int(0.05 * a.boot)] / 3600,
               "cpu_h_hi": L * bs[int(0.95 * a.boot)] / 3600, "proof_tb": L * st.mean(pb) / 1e12,
               "top_sample_share": max(x) / sum(x), "max_checker_rss_mb": max(r.get("checker", {}).get("maxrss", 0) for r in rs) / 1024}
        rows.append(row)
        total["leaves"] += L; total["cpu_h"] += row["cpu_h"]; total["solver_h"] += L * row["mean_solver_s"] / 3600
        total["checker_h"] += L * row["mean_checker_s"] / 3600; total["proof_bytes"] += L * st.mean(pb); total["n"] += n
        total["capped"] += len(capped); total["not_certified"] += len(bad)
    boots.sort()
    lo, hi = boots[int(0.05 * a.boot)], boots[int(0.95 * a.boot)]
    # Fixed per-leaf overhead: the cheapest decile of leaves is essentially parse-only.
    allx = sorted((r["solver"]["cpu_seconds"], r["checker"]["cpu_seconds"]) for rs in by.values() for r in rs if r["status"] == "CERTIFIED")
    k = max(1, len(allx) // 10)
    fixed_solver = st.mean(s for s, _ in allx[:k]); fixed_checker = min(c for _, c in allx)
    fixed_h = total["leaves"] * (fixed_solver + fixed_checker) / 3600
    # Hill estimator on the pooled sample (each value / its cube mean), top 5%.
    pooled_norm.sort(reverse=True)
    kk = max(5, len(pooled_norm) // 20)
    hill = kk / sum(math.log(pooled_norm[i] / pooled_norm[kk]) for i in range(kk)) if pooled_norm[kk] > 0 else float("nan")
    cap = max((r.get("cap_seconds", 3600) for r in recs), default=3600)
    r3 = 3.0 / max(1, total["n"])  # 95% upper bound on the capped fraction if none was seen (pooled, unweighted)

    def usd(cpu_h: float, rate: float) -> float:
        return cpu_h / UTILISATION * rate

    summary = {"schema": "erdos85-h7-hsb-estimate-v1", "sampled_leaves": total["n"], "leaves": total["leaves"], "cap_seconds": cap,
               "capped_samples": total["capped"], "non_certified_non_capped_samples": total["not_certified"],
               "cpu_hours": round(total["cpu_h"]), "cpu_hours_5_95": [round(lo), round(hi)],
               "solver_cpu_hours": round(total["solver_h"]), "checker_cpu_hours": round(total["checker_h"]),
               "fixed_overhead_cpu_s_per_leaf": round(fixed_solver + fixed_checker, 2), "fixed_overhead_cpu_hours": round(fixed_h),
               "proof_tb_streamed": round(total["proof_bytes"] / 1e12, 1), "hill_tail_index_top5pct": round(hill, 2),
               "rule_of_three_capped_fraction_95": r3, "rule_of_three_capped_leaves_95": round(r3 * total["leaves"]),
               "utilisation_assumed": UTILISATION,
               "usd_spot": [round(usd(v, SPOT_PER_VCPU_H)) for v in (lo, total["cpu_h"], hi)],
               "usd_builder_on_demand": [round(usd(v, BUILDER_PER_VCPU_H)) for v in (lo, total["cpu_h"], hi)],
               "covers": {"count": len(covers), "certified": sum(r["status"] == "CERTIFIED" for r in covers),
                          "solver_cpu_s": round(sum(r["solver"]["cpu_seconds"] for r in covers), 1),
                          "checker_cpu_s": round(sum(r["checker"]["cpu_seconds"] for r in covers), 1),
                          "max_solver_cpu_s": round(max([r["solver"]["cpu_seconds"] for r in covers] or [0]), 1)},
               "cubes": rows}
    md = ["| cube | leaves | n | UNSAT+verified | capped | mean s | median s | p90 s | max s | mean conflicts | checker share | "
          "CPU-h (5%–95%) | proof TB | spot $ |", "|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|"]
    for r in rows:
        md.append(f"| {r['cube'][5:]} | {r['leaves']:,} | {r['sampled']} | {r['certified']} | {r['capped']} | {r['mean_s']:.1f} | "
                  f"{r['median_s']:.1f} | {r['p90_s']:.0f} | {r['max_s']:.0f} | {r['mean_conflicts'] / 1000:.0f}k | "
                  f"{100 * r['mean_checker_s'] / r['mean_s']:.0f}% | {r['cpu_h']:.0f} ({r['cpu_h_lo']:.0f}–{r['cpu_h_hi']:.0f}) | "
                  f"{r['proof_tb']:.2f} | {usd(r['cpu_h'], SPOT_PER_VCPU_H):.0f} |")
    md.append(f"| **total** | **{total['leaves']:,}** | {total['n']} | {sum(r['certified'] for r in rows)} | {total['capped']} | | | | | | "
              f"{100 * total['checker_h'] / total['cpu_h']:.0f}% | **{total['cpu_h']:.0f} ({lo:.0f}–{hi:.0f})** | "
              f"**{total['proof_bytes'] / 1e12:.1f}** | **{usd(total['cpu_h'], SPOT_PER_VCPU_H):.0f}** |")
    text = "\n".join(md) + "\n"
    if a.md:
        a.md.write_text(text)
    if a.json:
        a.json.write_text(json.dumps(summary, indent=1) + "\n")
    print(text)
    print(json.dumps({k: v for k, v in summary.items() if k != "cubes"}, indent=1))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
