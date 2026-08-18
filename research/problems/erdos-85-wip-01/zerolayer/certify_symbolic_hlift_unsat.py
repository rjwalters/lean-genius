#!/usr/bin/env python3
"""Promote an exact symbolic H-lift signal-UNSAT CNF to a DRAT certificate."""

import argparse
import json
from pathlib import Path
import shutil
import subprocess

from run_hlift_orbit_signal import parse_status, sha256_file


def executable_provenance(command):
    resolved = shutil.which(command)
    if resolved is None:
        raise SystemExit(f"executable not found: {command}")
    return {"path": str(Path(resolved).resolve()),
            "sha256": sha256_file(resolved)}


def drat_verified(path):
    with open(path, encoding="utf-8", errors="replace") as stream:
        return any(line.strip() == "s VERIFIED" for line in stream)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("result")
    parser.add_argument("--certificate-dir", required=True)
    parser.add_argument("--solver", default="kissat")
    parser.add_argument("--drat-trim", default="drat-trim")
    args = parser.parse_args()

    result_path = Path(args.result).resolve()
    signal = json.load(open(result_path, encoding="utf-8"))
    if signal["verdict"] != "SIGNAL_UNSAT_REQUIRES_PROOF_RERUN":
        raise SystemExit("result is not a symbolic signal-UNSAT instance")
    cnf = Path(signal["cnf"]).resolve()
    if sha256_file(cnf) != signal["cnf_sha256"]:
        raise SystemExit("preserved CNF hash mismatch")
    cert = Path(args.certificate_dir).resolve()
    cert.mkdir(parents=True, exist_ok=False)
    proof = cert / "proof.drat"
    solver_log = cert / "solver.log"
    solver_cmd = [args.solver, str(cnf), str(proof)]
    with open(solver_log, "w", encoding="utf-8") as stream:
        solved = subprocess.run(solver_cmd, stdout=stream,
                                stderr=subprocess.STDOUT, check=False)
    status = parse_status(solver_log)
    if status != "UNSATISFIABLE":
        raise SystemExit(f"proof rerun did not return UNSATISFIABLE: {status!r}")
    if not proof.is_file() or proof.stat().st_size == 0:
        raise SystemExit("solver returned UNSAT without a nonempty proof")

    verify_log = cert / "drat-trim.log"
    verify_cmd = [args.drat_trim, str(cnf), str(proof)]
    with open(verify_log, "w", encoding="utf-8") as stream:
        checked = subprocess.run(verify_cmd, stdout=stream,
                                 stderr=subprocess.STDOUT, check=False)
    if checked.returncode != 0 or not drat_verified(verify_log):
        raise SystemExit("drat-trim did not report `s VERIFIED` "
                         f"(exit {checked.returncode})")
    report = {
        "verdict": "SYMBOLIC_CLASS_UNSAT_DRAT_VERIFIED",
        "scope": signal["scope"],
        "cnf": str(cnf),
        "cnf_sha256": signal["cnf_sha256"],
        "signal_result": str(result_path),
        "signal_result_sha256": sha256_file(result_path),
        "manifest_sha256": signal["manifest_sha256"],
        "encoder_sha256": signal["encoder_sha256"],
        "verifier_sha256": signal["verifier_sha256"],
        "proof": str(proof),
        "proof_sha256": sha256_file(proof),
        "solver": executable_provenance(args.solver),
        "solver_command": solver_cmd,
        "solver_exit": solved.returncode,
        "drat_trim": executable_provenance(args.drat_trim),
        "drat_trim_command": verify_cmd,
        "drat_trim_exit": checked.returncode,
        "solver_log_sha256": sha256_file(solver_log),
        "drat_trim_log_sha256": sha256_file(verify_log),
    }
    with open(cert / "certificate.json", "w", encoding="utf-8") as stream:
        json.dump(report, stream, indent=1)
    print("SYMBOLIC_CLASS_UNSAT_DRAT_VERIFIED", cert)


if __name__ == "__main__":
    main()
