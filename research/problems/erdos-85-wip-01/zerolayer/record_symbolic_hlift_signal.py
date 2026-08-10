#!/usr/bin/env python3
"""Record a hash-pinned symbolic H-lift signal run.

The solver may have been launched separately on a remote host.  This consumer
checks that the preserved CNF and manifest agree, rejects conflicting status
lines, and independently verifies any SAT assignment.  A signal-run UNSAT is
only marked as requiring a proof-logged rerun on the exact same CNF.
"""

import argparse
import json
from pathlib import Path
import subprocess
import sys

from run_hlift_orbit_signal import parse_status, sha256_file


def validate_symbolic_manifest(manifest_path, cnf_path, verifier_path):
    doc = json.load(open(manifest_path, encoding="utf-8"))
    if doc.get("scope") != "all corrected Stage-1 (4,4,4,4) service witnesses":
        raise ValueError("unexpected symbolic manifest scope")
    actual_cnf = sha256_file(cnf_path)
    if doc.get("sha256") != actual_cnf:
        raise ValueError("CNF hash mismatch")
    actual_verifier = sha256_file(verifier_path)
    if doc.get("sat_verifier_sha256") != actual_verifier:
        raise ValueError("SAT verifier hash mismatch")
    with open(cnf_path, encoding="ascii") as stream:
        header = stream.readline().split()
    expected = ["p", "cnf", str(doc["vars"]), str(doc["clauses"])]
    if header != expected:
        raise ValueError(f"DIMACS header mismatch: {header!r} != {expected!r}")
    if sum(doc["rule_counts"].values()) != doc["clauses"]:
        raise ValueError("manifest rule counts do not sum to clause count")
    return doc


def main():
    here = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser()
    parser.add_argument("--cnf", required=True)
    parser.add_argument("--manifest", required=True)
    parser.add_argument("--solver-log", required=True)
    parser.add_argument("--output", required=True)
    parser.add_argument("--solver-command", default="",
                        help="exact launch command, recorded as provenance")
    args = parser.parse_args()

    cnf = Path(args.cnf).resolve()
    manifest_path = Path(args.manifest).resolve()
    solver_log = Path(args.solver_log).resolve()
    output = Path(args.output).resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    verifier = here / "verify_symbolic_hlift_assignment.py"
    doc = validate_symbolic_manifest(manifest_path, cnf, verifier)
    status = parse_status(solver_log)
    result = {
        "scope": doc["scope"],
        "cnf": str(cnf),
        "cnf_sha256": doc["sha256"],
        "manifest": str(manifest_path),
        "manifest_sha256": sha256_file(manifest_path),
        "encoder_sha256": doc["encoder_sha256"],
        "verifier_sha256": doc["sat_verifier_sha256"],
        "solver_log": str(solver_log),
        "solver_log_sha256": sha256_file(solver_log),
        "solver_command": args.solver_command,
        "solver_status": status,
    }
    if status == "SATISFIABLE":
        verify_log = output.with_suffix(output.suffix + ".verify.log")
        command = [sys.executable, str(verifier), str(solver_log)]
        with open(verify_log, "w", encoding="utf-8") as stream:
            checked = subprocess.run(command, stdout=stream,
                                     stderr=subprocess.STDOUT, check=False)
        result["verifier_command"] = command
        result["verifier_exit"] = checked.returncode
        result["verifier_log"] = str(verify_log)
        result["verifier_log_sha256"] = sha256_file(verify_log)
        option_checked = None
        if doc.get("options", {}).get("paired_type_quotient"):
            option_verifier = here / "verify_symbolic_paired_assignment.py"
            option_log = output.with_suffix(output.suffix + ".options.log")
            option_command = [sys.executable, str(option_verifier),
                              str(solver_log)]
            with open(option_log, "w", encoding="utf-8") as stream:
                option_checked = subprocess.run(
                    option_command, stdout=stream, stderr=subprocess.STDOUT,
                    check=False)
            result["option_verifier_sha256"] = sha256_file(option_verifier)
            result["option_verifier_command"] = option_command
            result["option_verifier_exit"] = option_checked.returncode
            result["option_verifier_log"] = str(option_log)
            result["option_verifier_log_sha256"] = sha256_file(option_log)
        verified = checked.returncode == 0 and (
            option_checked is None or option_checked.returncode == 0)
        result["verdict"] = ("RELAXATION_SAT_VERIFIED" if verified
                             else "SAT_VERIFICATION_FAILED")
    elif status == "UNSATISFIABLE":
        result["verdict"] = "SIGNAL_UNSAT_REQUIRES_PROOF_RERUN"
    elif status is None or status == "UNKNOWN":
        result["verdict"] = "UNKNOWN"
    else:
        result["verdict"] = "UNRECOGNIZED_SOLVER_STATUS"
    with open(output, "w", encoding="utf-8") as stream:
        json.dump(result, stream, indent=1)
    print(result["verdict"], output)


if __name__ == "__main__":
    main()
