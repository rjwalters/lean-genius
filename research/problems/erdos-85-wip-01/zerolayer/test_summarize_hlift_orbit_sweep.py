#!/usr/bin/env python3
"""Positive and incomplete-path tests for the strict sweep aggregator."""

import json
from pathlib import Path
import tempfile

from summarize_hlift_orbit_sweep import summarize

SHA = "a" * 64
with tempfile.TemporaryDirectory() as root:
    root = Path(root)
    for index in range(2):
        job = root / f"orbit_{index:03d}"
        cert = job / "certificate"
        cert.mkdir(parents=True)
        result = {"artifact_sha256": SHA, "orbit_index": index,
                  "cnf_sha256": str(index) * 64,
                  "verdict": "SIGNAL_UNSAT_REQUIRES_PROOF_RERUN"}
        (job / "result.json").write_text(json.dumps(result))
        certificate = {"verdict": "UNSAT_DRAT_VERIFIED",
                       "artifact_sha256": SHA, "orbit_index": index,
                       "cnf_sha256": str(index) * 64}
        (cert / "certificate.json").write_text(json.dumps(certificate))
    report = summarize(root, SHA, 2)
    assert report["outcome"] == "ALL_ORBITS_UNSAT_DRAT_VERIFIED"
    (root / "orbit_001" / "certificate" / "certificate.json").unlink()
    report = summarize(root, SHA, 2)
    assert report["outcome"] == "INCOMPLETE_NO_CLASS_CONCLUSION"
    assert report["verdict_counts"]["SIGNAL_UNSAT_REQUIRES_PROOF_RERUN"] == 1
    result_path = root / "orbit_001" / "result.json"
    result = json.loads(result_path.read_text())
    result["verdict"] = "RELAXATION_SAT_VERIFIED"
    result_path.write_text(json.dumps(result))
    report = summarize(root, SHA, 2)
    assert report["outcome"] == "RELAXATION_SAT_EXISTS_CLASS_NOT_KILLED"
print("ALL OK")
