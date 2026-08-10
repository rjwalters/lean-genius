#!/usr/bin/env python3
"""Toy trajectory test for the sparse PSD-cut log summarizer."""

import json
from pathlib import Path
import subprocess
import sys
import tempfile


with tempfile.TemporaryDirectory() as raw:
    root = Path(raw)
    log = root / "cuts.log"
    log.write_text(
        "lp_direct_compiled 9.5\n"
        "lp_direct_data_keys ['A', 'b', 'dims']\n"
        "lp_direct_iteration 0 status kOptimal time 2.5\n"
        "lp_direct_unpack_audit Y00 1.0 forced_zero_row_max 0.0 "
        "max_primal_infeasibility 1e-9\n"
        "lp_direct_min_eigenvalue -10.0\n"
        "lp_direct_cut 0 value -4.5 [(1, 3), (4, -2)]\n"
        "lp_direct_iteration 1 status kOptimal time 8.0\n"
        "lp_direct_unpack_audit Y00 1.0 forced_zero_row_max 0.0 "
        "max_primal_infeasibility 1e-9\n"
        "lp_direct_min_eigenvalue -3.0\n"
        "lp_direct_cut 1 value -1.25 [(1, 2), (7, 5)]\n"
        "lp_direct_iteration 2 status kOptimal time 12.0\n"
        "lp_direct_unpack_audit Y00 1.0 forced_zero_row_max 0.0 "
        "max_primal_infeasibility 1e-9\n"
        "lp_direct_min_eigenvalue -5.0\n"
        "integer_cuts [[(1, 3)], [(7, 5)]]\n")
    output = root / "summary.json"
    script = Path(__file__).with_name("summarize_sparse_lp_cuts.py")
    subprocess.run([sys.executable, str(script), str(log), "--output", str(output),
                    "--expected-cuts", "2"],
                   check=True, capture_output=True, text=True)
    report = json.loads(output.read_text())
    assert report["optimal_iterations"] == 3
    assert report["compile_seconds"] == 9.5
    assert report["data_keys"] == ["A", "b", "dims"]
    assert report["traceback_detected"] is False
    assert report["normal_completion_marker"] is True
    assert report["trajectory_complete"] is True
    assert report["unpack_audited_iterations"] == 3
    assert report["unpack_audit_passed"] is True
    assert report["trajectory_usable"] is True
    assert report["expected_cuts"] == 2
    assert report["terminal_status"] == "kOptimal"
    assert report["cuts"] == 2
    assert report["least_negative_min_eigenvalue"] == -3.0
    assert report["terminal_min_eigenvalue"] == -5.0
    assert report["support_frequency"][0] == {
        "index": 1, "label": "X[omit=0,copy=0,x=0]", "cuts": 2}
    assert report["iterations"][0]["support_decoded"][1] == {
        "index": 4, "label": "X[omit=0,copy=0,x=3]", "coefficient": -2}
    assert report["support_frequency_by_family"] == [
        {"family": "X", "cuts": 4}]
    assert report["support_frequency_by_orphan"] == [
        {"orphan": "X[omit=0,copy=0]", "cuts": 4}]

print("SPARSE LP CUT SUMMARY ALL OK")
