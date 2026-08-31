#!/usr/bin/env python3
"""Verify the small-high fleet selectors against the live Lean definitions."""

from __future__ import annotations

import argparse
import importlib.util
import json
import re
import subprocess
import tempfile
from pathlib import Path


HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
PROOFS = REPO / "proofs"
JOBS_SCRIPT = HERE / "generate_small_high_cube_jobs.py"
BEGIN = "ERDOS85_SELECTOR_CONTRACT_BEGIN"
END = "ERDOS85_SELECTOR_CONTRACT_END"


def load_python_selectors() -> dict[str, tuple[tuple[int, ...], tuple[int, ...]]]:
    spec = importlib.util.spec_from_file_location("small_high_jobs", JOBS_SCRIPT)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module.SELECTORS


def lean_source() -> str:
    return f'''import Proofs.Erdos85OrderFortyNineSmallHighCubeCover

open Erdos85

#eval IO.println "{BEGIN}"
#eval orderFortyNineThreeHighCubeCells.map (fun cell =>
  ((orderFortyNineThreeHighCubeLeftVariables cell.2).map (· + 1),
   (orderFortyNineThreeHighCubeRightVariables cell.2).map (· + 1)))
#eval orderFortyNineFiveHighCubeCells.map (fun cell =>
  ((orderFortyNineFiveHighCubeLeftVariables cell.2).map (· + 1),
   (orderFortyNineFiveHighCubeRightVariables cell.2).map (· + 1)))
#eval IO.println "{END}"
'''


def parse_lean_values(stdout: str) -> list[int]:
    if stdout.count(BEGIN) != 1 or stdout.count(END) != 1:
        raise ValueError("Lean selector output delimiters are missing or duplicated")
    body = stdout.split(BEGIN, 1)[1].split(END, 1)[0]
    return [int(value) for value in re.findall(r"\d+", body)]


def expected_values(selectors: dict[str, tuple[tuple[int, ...], tuple[int, ...]]]
                    ) -> list[int]:
    order = ("h3_b1", "h3_c1", "h3_c2", "h3_dist2",
             "h5_t0", "h5_t1", "h5_t2")
    if set(selectors) != set(order):
        raise ValueError("Python selector table does not contain exactly seven cells")
    return [literal for cell in order for side in selectors[cell]
            for literal in side]


def run_lean(proofs_dir: Path = PROOFS) -> subprocess.CompletedProcess[str]:
    with tempfile.TemporaryDirectory(prefix=".selector-contract-",
                                     dir=proofs_dir) as raw:
        source = Path(raw) / "Check.lean"
        source.write_text(lean_source())
        return subprocess.run(
            ["lake", "env", "lean", str(source)], cwd=proofs_dir,
            text=True, capture_output=True, check=False)


def validate(proofs_dir: Path = PROOFS) -> dict[str, object]:
    selectors = load_python_selectors()
    result = run_lean(proofs_dir)
    if result.returncode != 0:
        raise ValueError(f"Lean selector evaluation failed:\n{result.stderr}")
    actual = parse_lean_values(result.stdout)
    expected = expected_values(selectors)
    if actual != expected:
        mismatch = next((index for index, pair in enumerate(zip(actual, expected))
                         if pair[0] != pair[1]), min(len(actual), len(expected)))
        raise ValueError(
            "Python/Lean selector mismatch at flattened index "
            f"{mismatch}: Lean count={len(actual)}, Python count={len(expected)}")
    return {
        "schema": "erdos85-small-high-selector-contract-v1",
        "status": "PASS",
        "cells": len(selectors),
        "selector_literals": len(actual),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--proofs-dir", type=Path, default=PROOFS)
    args = parser.parse_args()
    print(json.dumps(validate(args.proofs_dir.resolve()), sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
