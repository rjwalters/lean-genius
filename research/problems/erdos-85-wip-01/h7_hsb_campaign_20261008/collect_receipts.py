#!/usr/bin/env python3
"""Fold the campaign's per-batch receipt files into per-cube evidence tables and check completeness.

    collect_receipts.py --inputs DIR --results DIR [--out DIR]

For every structural cube: the cover CNF and every leaf 0..n-1 must have a CERTIFIED receipt whose
cnf_sha256 equals the value recomputed from the pinned inputs, whose checker saw `s VERIFIED UNSAT`
and whose solver/checker binaries are the pinned ones. Writes <out>/<cube>.receipts.tsv.zst (one
line per leaf) and <out>/summary.json. Exit 0 only if all 28 cubes are complete.
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import h7_common as hc  # noqa: E402

CADICAL = "fd601b827c2f6e72c255dd27d6bfa9d7f982414181195fe3ea07ec81385772a2"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--inputs", type=Path, required=True)
    ap.add_argument("--results", type=Path, required=True)
    ap.add_argument("--out", type=Path)
    ap.add_argument("--cubes", default="")
    a = ap.parse_args()
    by_cube: dict[str, list[dict]] = {}
    files = sorted(a.results.glob("*.jsonl.zst"))
    for f in files:
        raw = subprocess.run(["zstd", "-dc", str(f)], capture_output=True, check=True).stdout
        for line in raw.decode().splitlines():
            r = json.loads(line)
            r["_file"] = f.name
            by_cube.setdefault(r["cube"], []).append(r)
    names = [c for c in hc.CUBES if not a.cubes or c in a.cubes.split(",")]
    summary = {"schema": "erdos85-h7-hsb-campaign-summary-v1", "result_files": len(files), "cubes": {}, "all_complete": True,
               "inputs_json_sha256": hc.sha_file(a.inputs / "inputs.json")}
    cakes = set()
    for name in names:
        cube = hc.Cube(a.inputs, name)
        best: dict = {}
        rejected = other = 0
        for r in by_cube.get(name, []):
            key = "cover" if r["kind"] == "cover" else r["leaf"]
            want = cube.meta["cover_cnf_sha256"] if key == "cover" else cube.leaf_sha256(key)
            good = (r["status"] == "CERTIFIED" and r.get("cnf_sha256") == want and r.get("binaries", {}).get("cadical") == CADICAL
                    and r.get("checker", {}).get("verified_line") is True and r.get("solver", {}).get("returncode") == 20
                    and not r.get("proof", {}).get("checker_closed_early"))
            if good:
                cakes.add(r["binaries"]["cake_lpr"])
                best.setdefault(key, r)
            elif r["status"] in ("CHECK_FAILED", "SOLVER_SAT"):
                rejected += 1
            else:
                other += 1
        missing = [n for n in range(cube.n_leaves) if n not in best]
        rows = [best[n] for n in range(cube.n_leaves) if n in best]
        c = {"leaves": cube.n_leaves, "certified_leaves": len(rows), "missing_leaves": len(missing), "first_missing": missing[:20],
             "cover_certified": "cover" in best, "alarm_receipts": rejected, "other_non_certified_receipts": other,
             "proof_bytes": sum(r["proof"]["bytes"] for r in rows), "solver_cpu_hours": round(sum(r["solver"]["cpu_seconds"] for r in rows) / 3600, 2),
             "checker_cpu_hours": round(sum(r["checker"]["cpu_seconds"] for r in rows) / 3600, 2),
             "max_solver_cpu_seconds": round(max([r["solver"]["cpu_seconds"] for r in rows] or [0]), 1),
             "complete": not missing and "cover" in best and rejected == 0}
        summary["cubes"][name] = c
        summary["all_complete"] = summary["all_complete"] and c["complete"]
        if a.out:
            a.out.mkdir(parents=True, exist_ok=True)
            lines = ["cube\tleaf\tcnf_sha256\tproof_sha256\tproof_bytes\tsolver_cpu_s\tchecker_cpu_s\tconflicts\thost\tfile\n"]
            for key in (["cover"] if "cover" in best else []) + [n for n in range(cube.n_leaves) if n in best]:
                r = best[key]
                lines.append("\t".join(str(x) for x in (name, key, r["cnf_sha256"], r["proof"]["sha256"], r["proof"]["bytes"],
                                                        round(r["solver"]["cpu_seconds"], 2), round(r["checker"]["cpu_seconds"], 2),
                                                        r["solver"].get("conflicts"), r["host"], r["_file"])) + "\n")
            subprocess.run(["zstd", "-q", "-19", "-f", "-o", str(a.out / f"{name}.receipts.tsv.zst")], input="".join(lines).encode(), check=True)
    summary["cake_lpr_sha256"] = sorted(cakes)
    summary["totals"] = {k: round(sum(c[k] for c in summary["cubes"].values()), 2) for k in
                         ("leaves", "certified_leaves", "missing_leaves", "proof_bytes", "solver_cpu_hours", "checker_cpu_hours")}
    text = json.dumps(summary, indent=1, sort_keys=True) + "\n"
    if a.out:
        (a.out / "summary.json").write_text(text)
    print(text if len(names) < 6 else json.dumps({"all_complete": summary["all_complete"], "totals": summary["totals"]}))
    return 0 if summary["all_complete"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
