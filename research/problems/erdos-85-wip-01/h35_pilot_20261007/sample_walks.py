#!/usr/bin/env python3
"""Knuth random-walk sampler of a partition-clause cube tree for one Lean-exact H3/H5 cell.

Branching rule (structural, Lean-coverable as a CubeTree): every cell CNF contains one
"partition clause" per (low vertex y, high vertex w) -- a positive clause of 7-8 edge literals
saying y has a neighbour in w's partition class (220 clauses for H5, 138 for H3; these are the
selectors of the existing Lean 7x8 grid `Erdos85OrderFortyNineSmallHighCubeCover`).
At a cube c (a set of positive edge literals), unit-propagate base units + c, then pick the
unsatisfied partition clause with the fewest non-falsified literals (fail-first, ties by clause
order), drop the literals whose assertion is a UP conflict (those leaves are trivially refuted),
and branch on the survivors. As a binary CubeTree this is split x1 / (not x1: split x2 / ...),
whose all-negative branch is refuted by UP of the partition clause.

A walk picks a uniformly random surviving literal at each level and records the branching
factors b_i; W_k = prod_{i<k} b_i is an unbiased estimator of the number of depth-k nodes (Knuth
1975), and mean(W_k * t(cube_k)) estimates the total solve time of the depth-k frontier.
"""
import argparse, json, random, sys, time
from pathlib import Path
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "phase_b_h1_verdict_cloud_20260921"))
import cube_split  # noqa: E402


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("cnf", type=Path); ap.add_argument("--walks", type=int, default=20); ap.add_argument("--first-walk", type=int, default=0)
    ap.add_argument("--depth", type=int, default=10); ap.add_argument("--seed", type=int, default=20261007)
    ap.add_argument("--out", type=Path, required=True)
    a = ap.parse_args()
    t0 = time.time()
    clauses = cube_split.parse(a.cnf)
    prop = cube_split.Propagator(clauses)
    units = [c[0] for c in clauses if len(c) == 1]
    parts = [c for c in clauses if len(c) >= 7 and all(l > 0 for l in c)]
    walks = []
    for w in range(a.first_walk, a.first_walk + a.walks):
        rng = random.Random(f"{a.seed}-{w}")  # per-walk stream: walks can run in separate processes
        cube, steps = [], []
        for _ in range(a.depth):
            f, val = prop.probe(units + cube)
            if f == float("inf"):
                steps.append({"conflict": True}); break
            best = None
            for pi, pc in enumerate(parts):
                if any(val.get(l) is True for l in pc):
                    continue
                live = [l for l in pc if val.get(l) is not False]
                if best is None or len(live) < len(best[1]):
                    best = (pi, live)
            if best is None:
                steps.append({"all_satisfied": True}); break
            pi, live = best
            surv = [l for l in live if prop.probe(units + cube + [l])[0] != float("inf")]
            if not surv:
                steps.append({"clause": pi, "live": live, "survivors": [], "refuted_by_up": True}); break
            pick = rng.choice(surv)
            steps.append({"clause": pi, "live": live, "survivors": surv, "pick": pick, "forced_before": f})
            cube = cube + [pick]
        weights, W = [], 1
        for s in steps:
            if "pick" in s:
                W *= len(s["survivors"]); weights.append(W)
        walks.append({"walk": w, "cube": cube, "steps": steps, "W": weights})
        print(json.dumps({"walk": w, "cube": cube, "W": weights, "t": round(time.time() - t0)}), flush=True)
    a.out.write_text(json.dumps({"cnf": str(a.cnf), "seed": a.seed, "depth": a.depth, "partition_clauses": len(parts),
                                 "rule": "fail-first partition clause, UP-pruned survivors", "walks": walks}, indent=1))


if __name__ == "__main__":
    main()
