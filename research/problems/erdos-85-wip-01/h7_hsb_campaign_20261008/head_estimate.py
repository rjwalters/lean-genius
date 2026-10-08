#!/usr/bin/env python3
"""Head-corrected cost estimate: leaf cost against leaf INDEX.

    head_estimate.py --inputs-json receipts/inputs.json --sample receipts/sample_results_with_followup.jsonl \
        --profile receipts/head_profile.jsonl [--canary receipts/canary_head_leaves.json] [--json out] [--md out]

Per cube the leaves are cut into geometric index strata [0,1), [1,2), [2,4), [4,8), ... Every
observation of a leaf in a stratum counts (index profile, canary receipts, uniform cost sample);
stratum cost = stratum size x mean observed (solver + checker CPU). A capped leaf is counted at its
observed time, a LOWER bound, and reported. Strata without any observation take the mean of the
next observed stratum above (hardness falls with the index, so that is not an underestimate of
their relative order; flagged in the output).

Cubes without an index profile keep their uniform-sample estimate, multiplied by a head factor:
the ratio (stratified estimate) / (uniform-sample estimate) seen on the profiled cubes (pooled,
with the min and max ratio as the range).
"""
from __future__ import annotations

import argparse
import json
import statistics as st
from pathlib import Path

SPOT = 0.0147
UTIL = 0.85


def strata(n: int) -> list[tuple[int, int]]:
    out, lo = [(0, 1)], 1
    while lo < n:
        out.append((lo, min(n, 2 * lo)))
        lo *= 2
    return out


def cost(r: dict) -> float:
    return (r.get("solver", {}).get("cpu_seconds") or 0) + (r.get("checker", {}).get("cpu_seconds") or 0)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--inputs-json", type=Path, required=True)
    ap.add_argument("--sample", type=Path, required=True)
    ap.add_argument("--profile", type=Path, required=True)
    ap.add_argument("--canary", type=Path)
    ap.add_argument("--cap", type=float, default=7200)
    ap.add_argument("--json", type=Path)
    ap.add_argument("--md", type=Path)
    a = ap.parse_args()
    meta = json.loads(a.inputs_json.read_text())["cubes"]
    obs: dict[str, dict[int, dict]] = {c: {} for c in meta}  # cube -> leaf -> {cost, capped, src}

    def add(cube, leaf, c, capped, src, prio):
        cur = obs[cube].get(leaf)
        if cur is None or prio > cur["prio"]:
            obs[cube][leaf] = {"cost": c, "capped": capped, "src": src, "prio": prio}

    uniform: dict[str, list[float]] = {}
    for line in a.sample.read_text().splitlines():
        r = json.loads(line)
        if r["kind"] == "leaf":
            uniform.setdefault(r["cube"], []).append(cost(r))
            add(r["cube"], r["leaf"], cost(r), r["status"] == "SOLVER_TIMEOUT", "sample", 1)
    profiled = set()
    for line in a.profile.read_text().splitlines():
        r = json.loads(line)
        profiled.add(r["cube"])
        add(r["cube"], r["leaf"], cost(r), r["status"] == "SOLVER_TIMEOUT", "profile", 3)
    if a.canary and a.canary.exists():
        for key, r in json.loads(a.canary.read_text()).items():
            cube, leaf = key.split(":")
            if r["status"] in ("CERTIFIED", "SOLVER_TIMEOUT"):
                add(cube, int(leaf), (r["solver_cpu"] or 0) + (r["checker_cpu"] or 0), r["status"] == "SOLVER_TIMEOUT", "canary", 2)
    rows, ratios = [], {}
    for cube in meta:
        n = meta[cube]["leaves"]
        uni_h = n * st.mean(uniform[cube]) / 3600
        row = {"cube": cube, "leaves": n, "uniform_cpu_h": uni_h, "profiled": cube in profiled}
        if cube in profiled:
            ss, total, capped_leaves, capped_h, detail, pending = strata(n), 0.0, 0.0, 0.0, [], []
            for lo, hi in ss:
                v = [o for leaf, o in obs[cube].items() if lo <= leaf < hi]
                d = {"lo": lo, "hi": hi, "n_obs": len(v)}
                if v:
                    d["mean_s"] = st.mean(o["cost"] for o in v)
                    d["max_s"] = max(o["cost"] for o in v)
                    d["capped_obs"] = sum(o["capped"] for o in v)
                detail.append(d)
            # fill unobserved strata from the next observed stratum above
            for i in range(len(detail) - 1, -1, -1):
                if "mean_s" not in detail[i]:
                    nxt = next((x for x in detail[i + 1:] if "mean_s" in x), None) or next(x for x in reversed(detail[:i]) if "mean_s" in x)
                    detail[i].update(mean_s=nxt["mean_s"], max_s=None, capped_obs=0, filled=True)
            for d in detail:
                size = d["hi"] - d["lo"]
                d["cpu_h"] = size * d["mean_s"] / 3600
                total += d["cpu_h"]
                if d["n_obs"]:
                    frac = d["capped_obs"] / d["n_obs"]
                    capped_leaves += size * frac
                    capped_h += size * frac * a.cap / 3600
            head = sum(d["cpu_h"] for d in detail if d["hi"] <= 1024)
            row.update(stratified_cpu_h=total, head_cpu_h_first_1024=head, expected_capped_leaves=capped_leaves,
                       capped_cpu_h_counted=capped_h, ratio=total / uni_h, strata=detail,
                       observations=len(obs[cube]), max_s=max(o["cost"] for o in obs[cube].values()))
            ratios[cube] = total / uni_h
        rows.append(row)
    pooled = sum(r["stratified_cpu_h"] for r in rows if r["profiled"]) / sum(r["uniform_cpu_h"] for r in rows if r["profiled"])
    lo_r, hi_r = min(ratios.values()), max(ratios.values())
    tot = {"uniform": 0.0, "point": 0.0, "low": 0.0, "high": 0.0, "capped": 0.0}
    for r in rows:
        if r["profiled"]:
            p = l = h = r["stratified_cpu_h"]
            tot["capped"] += r["expected_capped_leaves"]
        else:
            p, l, h = r["uniform_cpu_h"] * pooled, r["uniform_cpu_h"] * min(1.0, lo_r), r["uniform_cpu_h"] * hi_r
        r.update(estimate_cpu_h=p, estimate_low=l, estimate_high=h)
        tot["uniform"] += r["uniform_cpu_h"]; tot["point"] += p; tot["low"] += l; tot["high"] += h
    capped_frac = tot["capped"] / max(1, sum(r["leaves"] for r in rows if r["profiled"]))
    unprofiled_leaves = sum(r["leaves"] for r in rows if not r["profiled"])
    summary = {"schema": "erdos85-h7-hsb-head-estimate-v1", "profiled_cubes": sorted(profiled), "pooled_head_factor": pooled,
               "head_factor_range": [lo_r, hi_r], "uniform_sample_cpu_h": tot["uniform"], "head_corrected_cpu_h": tot["point"],
               "head_corrected_cpu_h_range": [tot["low"], tot["high"]],
               "expected_capped_leaves_profiled_cubes": tot["capped"],
               "expected_capped_leaves_all_cubes_if_same_rate": tot["capped"] + capped_frac * unprofiled_leaves,
               "usd_spot": [round(v / UTIL * SPOT) for v in (tot["low"], tot["point"], tot["high"])], "cubes": rows}
    md = ["| cube | leaves | uniform-sample CPU-h | index profile | obs | head (first 1,024 leaves) CPU-h | head-corrected CPU-h | factor | max s | expected leaves > cap |",
          "|---|---:|---:|---|---:|---:|---:|---:|---:|---:|"]
    for r in rows:
        if r["profiled"]:
            md.append(f"| {r['cube'][5:]} | {r['leaves']:,} | {r['uniform_cpu_h']:.0f} | yes | {r['observations']} | {r['head_cpu_h_first_1024']:.0f} | "
                      f"**{r['stratified_cpu_h']:.0f}** | {r['ratio']:.2f} | {r['max_s']:.0f} | {r['expected_capped_leaves']:.0f} |")
        else:
            md.append(f"| {r['cube'][5:]} | {r['leaves']:,} | {r['uniform_cpu_h']:.0f} | no | | | {r['estimate_cpu_h']:.0f} "
                      f"({r['estimate_low']:.0f}–{r['estimate_high']:.0f}) | ×{pooled:.2f} | | |")
    md.append(f"| **total** | | **{tot['uniform']:.0f}** | | | | **{tot['point']:.0f} ({tot['low']:.0f}–{tot['high']:.0f})** | | | "
              f"{summary['expected_capped_leaves_all_cubes_if_same_rate']:.0f} |")
    text = "\n".join(md) + "\n"
    if a.md:
        a.md.write_text(text)
    if a.json:
        a.json.write_text(json.dumps(summary, indent=1) + "\n")
    print(text)
    for r in rows:
        if r["profiled"]:
            print(r["cube"], " ".join(f"[{d['lo']},{d['hi']}):{d['mean_s']:.0f}s×{d['n_obs']}{'*' if d.get('filled') else ''}{'!' * d.get('capped_obs', 0)}" for d in r["strata"]))
    print(json.dumps({k: v for k, v in summary.items() if k != "cubes"}, indent=1))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
