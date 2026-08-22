#!/usr/bin/env python3
"""Aggregate the unrestricted q=9 order-16 uniform twist exclusions.

Ten of the thirteen closing-twist classes are already impossible without
using any F20/A5/S5 point-stabilizer information.  This harness gives those
ten direct-CNF runs one fail-closed aggregate gate.  The remaining classes
0, 3, and 12 are intentionally handled by the stabilizer-specific sweeps.
"""

from __future__ import annotations

import argparse
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path


EASY_ROTATION_CLASSES = (1, 2, 4, 5, 6, 7, 8, 9, 10, 11)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("census", type=Path)
    parser.add_argument("--jobs", type=int, default=1)
    parser.add_argument("--kissat-seed", type=int, default=0)
    args = parser.parse_args()
    verifier = Path(__file__).with_name("q9_order16_endpoint_lift_sat.py")

    def check(rotation_class: int) -> int:
        command = [
            sys.executable,
            str(verifier),
            str(args.census),
            "--quotient", "uniform",
            "--rotation-class", str(rotation_class),
            "--encoding", "direct",
            "--backend", "kissat",
            "--kissat-mode", "unsat",
            "--kissat-seed", str(args.kissat_seed),
        ]
        process = subprocess.run(command, text=True, capture_output=True)
        expected = (
            "UNSAT backend=kissat rounds=0\n"
            f"excluded_quotient=uniform rotation_class={rotation_class}"
        )
        if process.returncode != 0 or expected not in process.stdout:
            raise RuntimeError(
                f"rotation_class={rotation_class} status={process.returncode}\n"
                f"stdout:\n{process.stdout}\nstderr:\n{process.stderr}"
            )
        return rotation_class

    completed = []
    with ThreadPoolExecutor(max_workers=args.jobs) as executor:
        futures = {
            executor.submit(check, rotation_class): rotation_class
            for rotation_class in EASY_ROTATION_CLASSES
        }
        for future in as_completed(futures):
            rotation_class = future.result()
            completed.append(rotation_class)
            print(
                f"completed_rotation_class={rotation_class} "
                f"count={len(completed)}/{len(EASY_ROTATION_CLASSES)}",
                flush=True,
            )
    assert sorted(completed) == list(EASY_ROTATION_CLASSES)
    print("UNSAT unrestricted_uniform_rotation_classes=10")
    print("remaining_rotation_classes=0,3,12")


if __name__ == "__main__":
    main()
