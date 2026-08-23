#!/usr/bin/env python3
"""Classify minimized residual degree cores across q=9 outer models.

This orchestrates ``q9_relation_base_benders_probe.py`` with residual C4
removed, so every reported core uses only exact degrees, mutual trace
eligibility, symmetry, and block-intersection orthogonality.  The result is a
sampled outer-design diagnostic, not a uniform proof.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path


HERE = Path(__file__).resolve().parent
PROBE = HERE / "q9_relation_base_benders_probe.py"


def tagged(output: str, prefix: str) -> str:
    for line in output.splitlines():
        if line.startswith(prefix):
            return line[len(prefix):]
    raise RuntimeError(f"missing {prefix!r} in probe output:\n{output}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--seeds", type=int, default=5)
    parser.add_argument("--timeout-seconds", type=int, default=120)
    parser.add_argument("--write-json", type=Path)
    args = parser.parse_args()
    if args.seeds <= 0:
        parser.error("--seeds must be positive")

    records = []
    for branch in (3, 4):
        for seed in range(args.seeds):
            command = [
                sys.executable, str(PROBE),
                "--branch", str(branch),
                "--random-seed", str(seed),
                "--timeout-seconds", str(args.timeout_seconds),
                "--degree-core", "--minimize-degree-core",
                "--relax-inner", "residual-c4",
            ]
            result = subprocess.run(
                command, text=True, capture_output=True, check=False,
            )
            if result.returncode != 0:
                raise RuntimeError(
                    f"probe failed for branch={branch} seed={seed}:\n"
                    + result.stdout + result.stderr
                )
            if tagged(result.stdout, f"branch={branch} result=") != "unsat":
                raise RuntimeError(
                    f"expected UNSAT for branch={branch} seed={seed}:\n"
                    + result.stdout
                )
            core = json.loads(tagged(result.stdout, "degree_core="))
            profiles = json.loads(tagged(
                result.stdout, "degree_core_profiles="))
            intersections = json.loads(tagged(
                result.stdout, "degree_core_intersections="))
            common_points = None
            if core:
                blocks = [set(profiles[str(row)]["block"]) for row in core]
                common_points = sorted(set.intersection(*blocks))
            record = {
                "branch": branch,
                "seed": seed,
                "fingerprint": tagged(result.stdout, "outer_fingerprint="),
                "core": core,
                "core_size": len(core),
                "common_points": common_points,
                "intersections": intersections,
                "profiles": profiles,
            }
            records.append(record)
            print(json.dumps(record, sort_keys=True, separators=(",", ":")))

    sizes = {
        str(branch): [record["core_size"] for record in records
                      if record["branch"] == branch]
        for branch in (3, 4)
    }
    summary = {
        "models": len(records),
        "all_unsat": True,
        "core_sizes": sizes,
        "maximum_core_size": max(record["core_size"] for record in records),
        "single_row_cores": sum(record["core_size"] == 1
                                for record in records),
        "two_row_cores": sum(record["core_size"] == 2
                             for record in records),
        "five_row_cores": sum(record["core_size"] == 5
                              for record in records),
        "common_point_cores": sum(bool(record["common_points"])
                                  for record in records),
        "multirow_common_point_cores": sum(
            record["core_size"] > 1 and bool(record["common_points"])
            for record in records
        ),
        "disjoint_two_row_cores": sum(
            record["core_size"] == 2 and not record["intersections"]
            for record in records
        ),
    }
    print("summary=" + json.dumps(summary, sort_keys=True,
                                   separators=(",", ":")))
    if args.write_json is not None:
        args.write_json.write_text(json.dumps(
            {"records": records, "summary": summary}, indent=2,
            sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
