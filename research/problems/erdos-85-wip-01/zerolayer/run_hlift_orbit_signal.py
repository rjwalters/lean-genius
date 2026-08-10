#!/usr/bin/env python3
"""Generate and signal-solve one hash-pinned H-lift orbit instance.

This runner never treats a signal-run UNSAT line as a certificate.  SAT is
checked immediately by the independent edge-only verifier; UNSAT is recorded
as requiring an exact-CNF proof-logged rerun and drat-trim verification.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys


def sha256_file(path):
    digest = hashlib.sha256()
    with open(path, "rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def parse_status(path):
    statuses = []
    with open(path, encoding="utf-8", errors="replace") as stream:
        for line in stream:
            if line.startswith("s "):
                statuses.append(line[2:].strip())
    if len(set(statuses)) > 1:
        raise ValueError(f"conflicting solver statuses: {statuses}")
    return statuses[-1] if statuses else None


def validate_manifest(manifest_path, cnf_path, artifact_sha, orbit_index):
    doc = json.load(open(manifest_path, encoding="utf-8"))
    provenance = doc["witness_provenance"]
    assert provenance["orbit_artifact_sha256"] == artifact_sha
    assert provenance["orbit_index"] == orbit_index
    assert doc["sha256"] == sha256_file(cnf_path), "CNF hash mismatch"
    return doc


def main():
    here = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser()
    parser.add_argument("--artifact", required=True)
    parser.add_argument("--artifact-sha256", required=True)
    parser.add_argument("--orbit-index", required=True, type=int)
    parser.add_argument("--solver", default="kissat")
    parser.add_argument("--timeout", type=int, default=3600)
    parser.add_argument("--output-root", required=True)
    parser.add_argument("--comm-anchor", action="store_true")
    args = parser.parse_args()

    artifact = str(Path(args.artifact).resolve())
    if sha256_file(artifact) != args.artifact_sha256:
        raise SystemExit("orbit artifact hash mismatch before generation")
    job = Path(args.output_root).resolve() / f"orbit_{args.orbit_index:03d}"
    job.mkdir(parents=True, exist_ok=False)
    encoder = here / "model4444_hlift.py"
    verifier = here / "verify_hlift_assignment.py"
    common = ["--wit-json", artifact,
              "--wit-sha256", args.artifact_sha256,
              "--orbit-index", str(args.orbit_index)]
    emit_cmd = [sys.executable, str(encoder), *common, "--emit"]
    if args.comm_anchor:
        emit_cmd.append("--comm-anchor")
    with open(job / "emit.log", "w", encoding="utf-8") as log:
        emitted = subprocess.run(emit_cmd, cwd=job, stdout=log,
                                 stderr=subprocess.STDOUT, check=False)
    if emitted.returncode != 0:
        raise SystemExit(f"encoder failed with exit {emitted.returncode}")
    manifests = list(job.glob("hlift4444_*.manifest.json"))
    cnfs = list(job.glob("hlift4444_*.cnf"))
    if len(manifests) != 1 or len(cnfs) != 1:
        raise SystemExit("expected exactly one generated CNF and manifest")
    manifest = validate_manifest(manifests[0], cnfs[0],
                                 args.artifact_sha256, args.orbit_index)

    solver_cmd = [args.solver, f"--time={args.timeout}", str(cnfs[0])]
    solver_log = job / "solver.log"
    with open(solver_log, "w", encoding="utf-8") as log:
        solved = subprocess.run(solver_cmd, cwd=job, stdout=log,
                                stderr=subprocess.STDOUT, check=False)
    status = parse_status(solver_log)
    result = {
        "artifact_sha256": args.artifact_sha256,
        "orbit_index": args.orbit_index,
        "cnf": cnfs[0].name,
        "cnf_sha256": manifest["sha256"],
        "encoder_sha256": sha256_file(encoder),
        "verifier_sha256": sha256_file(verifier),
        "solver_command": solver_cmd,
        "solver_exit": solved.returncode,
        "solver_status": status,
    }
    if status == "SATISFIABLE":
        verify_cmd = [sys.executable, str(verifier), str(solver_log), *common]
        with open(job / "verify.log", "w", encoding="utf-8") as log:
            checked = subprocess.run(verify_cmd, cwd=job, stdout=log,
                                     stderr=subprocess.STDOUT, check=False)
        result["verifier_exit"] = checked.returncode
        result["verdict"] = ("RELAXATION_SAT_VERIFIED" if checked.returncode == 0
                             else "SAT_VERIFICATION_FAILED")
    elif status == "UNSATISFIABLE":
        result["verdict"] = "SIGNAL_UNSAT_REQUIRES_PROOF_RERUN"
    elif status is None or status == "UNKNOWN":
        result["verdict"] = "UNKNOWN"
    else:
        result["verdict"] = "UNRECOGNIZED_SOLVER_STATUS"
    with open(job / "result.json", "w", encoding="utf-8") as stream:
        json.dump(result, stream, indent=1)
    print(result["verdict"], job)


if __name__ == "__main__":
    main()
