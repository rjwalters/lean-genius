#!/usr/bin/env python3
"""Check fixed-fiber A5/S5 order-16 lift formulas modulo twist symmetry."""

from __future__ import annotations

import argparse
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

from q9_order16_endpoint_lift_sat import FIBER_PARTITIONS_4, component_ordinal_4
from q9_order16_f20_sweep import assignment_representatives, automorphism_data, compose


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("census", type=Path)
    parser.add_argument("--rotation-class", type=int, required=True)
    parser.add_argument(
        "--stabilizer", choices=("a5-star", "a5-triangle"), required=True
    )
    parser.add_argument("--jobs", type=int, default=1)
    args = parser.parse_args()

    component = component_ordinal_4(args.census.read_bytes())
    automorphisms, rotation_classes = automorphism_data(component)
    alpha, _ = rotation_classes[args.rotation_class]
    centralizer = [
        beta
        for beta in automorphisms
        if compose(beta, alpha) == compose(alpha, beta)
    ]
    branches = assignment_representatives(FIBER_PARTITIONS_4, centralizer)
    print(
        f"coverage rotation_class={args.rotation_class} "
        f"stabilizer={args.stabilizer} centralizer_order={len(centralizer)} "
        f"representatives={len(branches)}",
        flush=True,
    )
    verifier = Path(__file__).with_name("q9_order16_endpoint_lift_sat.py")

    def check(branch: tuple[int, int]):
        partition, bijection = branch
        process = subprocess.run(
            [
                sys.executable,
                str(verifier),
                str(args.census),
                "--quotient", "uniform",
                "--stabilizer", args.stabilizer,
                "--rotation-class", str(args.rotation_class),
                "--a5-fiber-partition", str(partition),
                "--a5-fiber-bijection", str(bijection),
                "--encoding", "direct",
                "--kissat-mode", "unsat",
            ],
            text=True,
            capture_output=True,
        )
        if process.returncode != 0 or "UNSAT backend=kissat rounds=0" not in process.stdout:
            raise RuntimeError(
                f"branch={branch} status={process.returncode}\n"
                f"{process.stdout}{process.stderr}"
            )
        return branch

    completed = 0
    with ThreadPoolExecutor(max_workers=args.jobs) as executor:
        futures = {executor.submit(check, branch): branch for branch in branches}
        for future in as_completed(futures):
            branch = future.result()
            completed += 1
            print(f"completed branch={branch} count={completed}/{len(branches)}", flush=True)
    assert completed == len(branches)
    print(
        f"UNSAT fixed_a5_representatives={completed} "
        f"rotation_class={args.rotation_class} stabilizer={args.stabilizer}"
    )


if __name__ == "__main__":
    main()
