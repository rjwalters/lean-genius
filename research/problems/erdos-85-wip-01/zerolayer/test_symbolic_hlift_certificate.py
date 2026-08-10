#!/usr/bin/env python3
"""Small semantic tests for symbolic H-lift evidence consumers."""

import hashlib
import json
from pathlib import Path
import tempfile

from certify_symbolic_hlift_unsat import drat_verified
from record_symbolic_hlift_signal import validate_symbolic_manifest


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    here = Path(__file__).resolve().parent
    verifier = here / "verify_symbolic_hlift_assignment.py"
    with tempfile.TemporaryDirectory() as raw:
        root = Path(raw)
        cnf = root / "x.cnf"
        cnf.write_bytes(b"p cnf 1 1\n1 0\n")
        manifest = root / "x.manifest.json"
        doc = {
            "scope": "all corrected Stage-1 (4,4,4,4) service witnesses",
            "encoder_sha256": "e" * 64,
            "sat_verifier_sha256": sha(verifier.read_bytes()),
            "vars": 1,
            "clauses": 1,
            "sha256": sha(cnf.read_bytes()),
            "rule_counts": {"unit": 1},
        }
        manifest.write_text(json.dumps(doc), encoding="utf-8")
        assert validate_symbolic_manifest(manifest, cnf, verifier) == doc
        cube = dict(doc,
                    scope=doc["scope"] + " AND tau[(0,0),2]=0",
                    cube_phase=0, cube_literal=18349,
                    cube_partition_verified=True)
        manifest.write_text(json.dumps(cube), encoding="utf-8")
        assert validate_symbolic_manifest(manifest, cnf, verifier) == cube
        for malformed in (
                dict(cube, cube_literal=18350),
                dict(cube, cube_partition_verified=False),
                dict(cube, cube_phase=1)):
            manifest.write_text(json.dumps(malformed), encoding="utf-8")
            try:
                validate_symbolic_manifest(manifest, cnf, verifier)
                raise AssertionError("malformed phase cube accepted")
            except ValueError as exc:
                assert "unexpected symbolic manifest scope" in str(exc)
        bad = dict(doc, sha256="0" * 64)
        manifest.write_text(json.dumps(bad), encoding="utf-8")
        try:
            validate_symbolic_manifest(manifest, cnf, verifier)
            raise AssertionError("bad CNF hash accepted")
        except ValueError as exc:
            assert "CNF hash mismatch" in str(exc)
        log = root / "drat.log"
        log.write_text("c prelude\ns VERIFIED\n", encoding="utf-8")
        assert drat_verified(log)
        log.write_text("s NOT VERIFIED\n", encoding="utf-8")
        assert not drat_verified(log)
    print("SYMBOLIC CERTIFICATE TESTS OK")


if __name__ == "__main__":
    main()
