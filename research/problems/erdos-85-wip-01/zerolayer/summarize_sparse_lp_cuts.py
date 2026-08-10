#!/usr/bin/env python3
"""Summarize a direct-HiGHS rational PSD-cut trajectory."""

import argparse
import ast
from collections import Counter
import json
from pathlib import Path

from run_hlift_orbit_signal import sha256_file


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("log", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    iterations = {}
    pending = None
    compile_seconds = None
    data_keys = None
    traceback_detected = False
    with open(args.log, encoding="utf-8", errors="replace") as stream:
        for raw in stream:
            line = raw.strip()
            if line == "Traceback (most recent call last):":
                traceback_detected = True
            elif line.startswith("lp_direct_compiled "):
                compile_seconds = float(line.split()[1])
            elif line.startswith("lp_direct_data_keys "):
                data_keys = ast.literal_eval(line.split(" ", 1)[1])
            elif line.startswith("lp_direct_iteration "):
                fields = line.split()
                pending = int(fields[1])
                iterations[pending] = {
                    "iteration": pending, "status": fields[3],
                    "runtime": float(fields[5]),
                }
            elif line.startswith("lp_direct_min_eigenvalue "):
                if pending is None:
                    raise ValueError("minimum eigenvalue precedes iteration")
                iterations[pending]["min_eigenvalue"] = float(line.split()[1])
            elif line.startswith("lp_direct_cut "):
                prefix, support_text = line.split(" [", 1)
                fields = prefix.split()
                iteration = int(fields[1])
                if iteration not in iterations:
                    raise ValueError("cut precedes iteration")
                support = ast.literal_eval("[" + support_text)
                iterations[iteration]["cut_value"] = float(fields[3])
                iterations[iteration]["support"] = support
                iterations[iteration]["support_size"] = len(support)

    ordered = [iterations[index] for index in sorted(iterations)]
    if [item["iteration"] for item in ordered] != list(range(len(ordered))):
        raise ValueError("iteration sequence is not contiguous from zero")
    support_frequency = Counter(
        index for item in ordered for index, _coefficient in item.get("support", []))
    eigenvalues = [item["min_eigenvalue"] for item in ordered
                   if "min_eigenvalue" in item]
    report = {
        "verdict": "SPARSE_RATIONAL_PSD_CUT_TRAJECTORY",
        "log": str(args.log.resolve()), "log_sha256": sha256_file(args.log),
        "compile_seconds": compile_seconds, "data_keys": data_keys,
        "traceback_detected": traceback_detected,
        "iterations": ordered,
        "optimal_iterations": sum(item["status"] == "kOptimal" for item in ordered),
        "cuts": sum("cut_value" in item for item in ordered),
        "least_negative_min_eigenvalue": max(eigenvalues) if eigenvalues else None,
        "terminal_min_eigenvalue": eigenvalues[-1] if eigenvalues else None,
        "terminal_status": ordered[-1]["status"] if ordered else None,
        "support_frequency": [
            {"index": index, "cuts": count}
            for index, count in sorted(support_frequency.items(),
                                       key=lambda pair: (-pair[1], pair[0]))
        ],
    }
    rendered = json.dumps(report, indent=1) + "\n"
    if args.output:
        args.output.write_text(rendered)
    print(rendered, end="")


if __name__ == "__main__":
    main()
