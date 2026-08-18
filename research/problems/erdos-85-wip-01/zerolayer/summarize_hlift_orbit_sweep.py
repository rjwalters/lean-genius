#!/usr/bin/env python3
"""Strictly aggregate distributed H-lift orbit jobs without overclaiming."""

import argparse
import json
from pathlib import Path


def summarize(root, artifact_sha256, orbit_count):
    records = {}
    for path in Path(root).glob("orbit_*/result.json"):
        result = json.load(open(path, encoding="utf-8"))
        if result["artifact_sha256"] != artifact_sha256:
            raise ValueError(f"artifact mismatch in {path}")
        index = result["orbit_index"]
        if not 0 <= index < orbit_count:
            raise ValueError(f"orbit index out of range in {path}")
        if index in records:
            raise ValueError(f"duplicate orbit result {index}")
        verdict = result["verdict"]
        if verdict == "SIGNAL_UNSAT_REQUIRES_PROOF_RERUN":
            cert_path = path.parent / "certificate" / "certificate.json"
            if cert_path.is_file():
                cert = json.load(open(cert_path, encoding="utf-8"))
                if (cert.get("verdict") == "UNSAT_DRAT_VERIFIED" and
                    cert.get("artifact_sha256") == artifact_sha256 and
                    cert.get("orbit_index") == index and
                    cert.get("cnf_sha256") == result.get("cnf_sha256")):
                    verdict = "UNSAT_DRAT_VERIFIED"
                else:
                    raise ValueError(f"certificate provenance mismatch at {index}")
        records[index] = verdict
    missing = sorted(set(range(orbit_count)) - set(records))
    counts = {}
    for verdict in records.values():
        counts[verdict] = counts.get(verdict, 0) + 1
    if not missing and counts == {"UNSAT_DRAT_VERIFIED": orbit_count}:
        outcome = "ALL_ORBITS_UNSAT_DRAT_VERIFIED"
    elif any(v == "RELAXATION_SAT_VERIFIED" for v in records.values()):
        outcome = "RELAXATION_SAT_EXISTS_CLASS_NOT_KILLED"
    else:
        outcome = "INCOMPLETE_NO_CLASS_CONCLUSION"
    return {"artifact_sha256": artifact_sha256,
            "orbit_count": orbit_count, "results_found": len(records),
            "missing": missing, "verdict_counts": counts,
            "outcome": outcome}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("root")
    parser.add_argument("--artifact-sha256", required=True)
    parser.add_argument("--orbit-count", required=True, type=int)
    parser.add_argument("--output")
    args = parser.parse_args()
    report = summarize(args.root, args.artifact_sha256, args.orbit_count)
    rendered = json.dumps(report, indent=1)
    if args.output:
        Path(args.output).write_text(rendered + "\n", encoding="utf-8")
    print(rendered)


if __name__ == "__main__":
    main()
