#!/usr/bin/env python3
"""Summarize a direct-HiGHS rational PSD-cut trajectory."""

import argparse
import ast
from collections import Counter
import json
from pathlib import Path

from run_hlift_orbit_signal import sha256_file

N = 192


def moment_index_label(index):
    """Decode an index in the fixed lifted vector (1, X, Z)."""
    if index == 0:
        return "constant"
    if 1 <= index <= N:
        family, vertex = "X", index - 1
    elif N + 1 <= index <= 2 * N:
        family, vertex = "Z", index - N - 1
    else:
        raise ValueError(f"moment index outside [0,{2 * N}]: {index}")
    orphan_index, coordinate = divmod(vertex, 12)
    omit, copy = divmod(orphan_index, 4)
    return f"{family}[omit={omit},copy={copy},x={coordinate}]"


def moment_index_parts(index):
    if index == 0:
        return "constant", None, None, None
    shifted = index - 1
    family = "X" if shifted < N else "Z"
    vertex = shifted % N
    orphan_index, coordinate = divmod(vertex, 12)
    omit, copy = divmod(orphan_index, 4)
    return family, omit, copy, coordinate


def ranked_counts(counter, key_name):
    return [{key_name: key, "cuts": count}
            for key, count in sorted(counter.items(),
                                     key=lambda pair: (-pair[1], pair[0]))]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("log", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--expected-cuts", type=int)
    args = parser.parse_args()

    iterations = {}
    pending = None
    compile_seconds = None
    data_keys = None
    direct_layout = None
    traceback_detected = False
    normal_completion_marker = False
    with open(args.log, encoding="utf-8", errors="replace") as stream:
        for raw in stream:
            line = raw.strip()
            if line == "Traceback (most recent call last):":
                traceback_detected = True
            elif line.startswith("integer_cuts "):
                normal_completion_marker = True
            elif line.startswith("lp_direct_compiled "):
                compile_seconds = float(line.split()[1])
            elif line.startswith("lp_direct_data_keys "):
                data_keys = ast.literal_eval(line.split(" ", 1)[1])
            elif line.startswith("lp_direct_layout "):
                fields = line.split()
                direct_layout = {
                    "name": fields[1], "equalities": int(fields[3]),
                    "inequalities": int(fields[5]),
                }
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
            elif line.startswith("lp_direct_unpack_audit "):
                if pending is None:
                    raise ValueError("unpack audit precedes iteration")
                fields = line.split()
                iterations[pending]["unpack_audit"] = {
                    "Y00": float(fields[2]),
                    "forced_zero_row_max": float(fields[4]),
                    "max_primal_infeasibility": float(fields[6]),
                }
            elif line.startswith("lp_direct_cut "):
                prefix, support_text = line.split(" [", 1)
                fields = prefix.split()
                iteration = int(fields[1])
                if iteration not in iterations:
                    raise ValueError("cut precedes iteration")
                support = ast.literal_eval("[" + support_text)
                iterations[iteration]["cut_value"] = float(fields[3])
                iterations[iteration]["support"] = support
                iterations[iteration]["support_decoded"] = [
                    {"index": index, "label": moment_index_label(index),
                     "coefficient": coefficient}
                    for index, coefficient in support
                ]
                iterations[iteration]["support_size"] = len(support)

    ordered = [iterations[index] for index in sorted(iterations)]
    if [item["iteration"] for item in ordered] != list(range(len(ordered))):
        raise ValueError("iteration sequence is not contiguous from zero")
    support_frequency = Counter(
        index for item in ordered for index, _coefficient in item.get("support", []))
    family_frequency = Counter()
    orphan_frequency = Counter()
    coordinate_frequency = Counter()
    for index, count in support_frequency.items():
        family, omit, copy, coordinate = moment_index_parts(index)
        family_frequency[family] += count
        if omit is not None:
            orphan_frequency[f"{family}[omit={omit},copy={copy}]"] += count
            coordinate_frequency[f"{family}[x={coordinate}]"] += count
    eigenvalues = [item["min_eigenvalue"] for item in ordered
                   if "min_eigenvalue" in item]
    cuts = sum("cut_value" in item for item in ordered)
    requested_cut_round_complete = (
        args.expected_cuts is None or cuts == args.expected_cuts or
        (eigenvalues and eigenvalues[-1] >= -1e-5))
    trajectory_complete = (normal_completion_marker and not traceback_detected and
                           requested_cut_round_complete)
    audited = [item["unpack_audit"] for item in ordered
               if "unpack_audit" in item]
    unpack_audit_passed = (len(audited) == len(ordered) and bool(ordered) and
                           all(abs(item["Y00"] - 1) <= 1e-5 and
                               item["forced_zero_row_max"] <= 1e-5
                               for item in audited))
    report = {
        "verdict": "SPARSE_RATIONAL_PSD_CUT_TRAJECTORY",
        "log": str(args.log.resolve()), "log_sha256": sha256_file(args.log),
        "compile_seconds": compile_seconds, "data_keys": data_keys,
        "direct_layout": direct_layout,
        "traceback_detected": traceback_detected,
        "normal_completion_marker": normal_completion_marker,
        "expected_cuts": args.expected_cuts,
        "trajectory_complete": trajectory_complete,
        "unpack_audited_iterations": len(audited),
        "unpack_audit_passed": unpack_audit_passed,
        "trajectory_usable": trajectory_complete and unpack_audit_passed,
        "iterations": ordered,
        "optimal_iterations": sum(item["status"] == "kOptimal" for item in ordered),
        "cuts": cuts,
        "least_negative_min_eigenvalue": max(eigenvalues) if eigenvalues else None,
        "terminal_min_eigenvalue": eigenvalues[-1] if eigenvalues else None,
        "terminal_status": ordered[-1]["status"] if ordered else None,
        "support_frequency": [
            {"index": index, "label": moment_index_label(index), "cuts": count}
            for index, count in sorted(support_frequency.items(),
                                       key=lambda pair: (-pair[1], pair[0]))
        ],
        "support_frequency_by_family": ranked_counts(family_frequency, "family"),
        "support_frequency_by_orphan": ranked_counts(orphan_frequency, "orphan"),
        "support_frequency_by_coordinate": ranked_counts(
            coordinate_frequency, "coordinate"),
    }
    rendered = json.dumps(report, indent=1) + "\n"
    if args.output:
        args.output.write_text(rendered)
    print(rendered, end="")


if __name__ == "__main__":
    main()
