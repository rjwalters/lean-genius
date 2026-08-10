#!/usr/bin/env python3
"""Unit tests for sweep-runner status and provenance helpers."""

import hashlib
import json
import os
import tempfile

from run_hlift_orbit_signal import parse_status, sha256_file, validate_manifest

with tempfile.TemporaryDirectory() as directory:
    cnf = os.path.join(directory, "x.cnf")
    log = os.path.join(directory, "solver.log")
    manifest = os.path.join(directory, "x.manifest.json")
    open(cnf, "wb").write(b"p cnf 0 0\n")
    digest = hashlib.sha256(b"p cnf 0 0\n").hexdigest()
    open(log, "w").write("c test\ns SATISFIABLE\n")
    assert parse_status(log) == "SATISFIABLE"
    assert sha256_file(cnf) == digest
    doc = {"sha256": digest, "witness_provenance": {
        "orbit_artifact_sha256": "a" * 64, "orbit_index": 7}}
    open(manifest, "w").write(json.dumps(doc))
    assert validate_manifest(manifest, cnf, "a" * 64, 7) == doc
    open(log, "w").write("s SATISFIABLE\ns UNSATISFIABLE\n")
    try:
        parse_status(log)
        raise AssertionError("conflicting statuses accepted")
    except ValueError as exc:
        assert "conflicting" in str(exc)
print("ALL OK")
