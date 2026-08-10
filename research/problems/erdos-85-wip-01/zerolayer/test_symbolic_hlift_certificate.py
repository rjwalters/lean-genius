#!/usr/bin/env python3
"""Small semantic tests for symbolic H-lift evidence consumers."""

import hashlib
import json
from pathlib import Path
import tempfile

from certify_symbolic_hlift_unsat import drat_verified
from record_symbolic_hlift_signal import validate_symbolic_manifest
from verify_symbolic_hlift_assignment import phase_variable_map


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
        mapping, _ = phase_variable_map()
        second_literals = [mapping[((1, 0), 2, phase)] for phase in range(3)]
        recursive = dict(cube,
            scope=(doc["scope"] + " AND tau[(0,0),2]=1" +
                   " AND tau[(1,0),2]=2"),
            cube_phase=2, cube_literal=second_literals[2],
            cube_ancestry=[
                {"anchor": "tau[(0,0),2]", "orphan": [0, 0],
                 "component": 2, "phase": 1, "literal": 18350,
                 "exhaustive_anchor_literals": [18349, 18350, 18351]},
                {"anchor": "tau[(1,0),2]", "orphan": [1, 0],
                 "component": 2, "phase": 2,
                 "literal": second_literals[2],
                 "exhaustive_anchor_literals": second_literals},
            ])
        manifest.write_text(json.dumps(recursive), encoding="utf-8")
        assert validate_symbolic_manifest(manifest, cnf, verifier) == recursive
        exact_literals = [mapping[((0, 1), 2, phase)]
                          for phase in range(12)]
        residue_entry = {
            "anchor": "tau[(0,1),2]", "orphan": [0, 1],
            "component": 2, "residue_modulus": 3, "residue": 1,
            "clause_literals": exact_literals[1::3],
            "exact_phase_literals": exact_literals,
        }
        residue_cube = dict(
            recursive,
            scope=recursive["scope"] + " AND tau[(0,1),2]%3=1",
            cube_ancestry=[*recursive["cube_ancestry"], residue_entry],
            cube_residue_modulus=3, cube_residue=1,
            cube_clause_literals=exact_literals[1::3],
            exact_phase_literals=exact_literals,
            exact_one_hot_verified=True,
            exact_pairwise_exclusions_verified=True,
        )
        manifest.write_text(json.dumps(residue_cube), encoding="utf-8")
        assert validate_symbolic_manifest(manifest, cnf, verifier) == residue_cube
        value_entry = {
            "anchor": "tau[(0,1),2]", "orphan": [0, 1],
            "component": 2, "value": 4,
            "literal": exact_literals[4],
            "exhaustive_value_literals": exact_literals[1::3],
        }
        value_cube = dict(
            residue_cube,
            scope=residue_cube["scope"] + " AND tau[(0,1),2]=4",
            cube_ancestry=[*residue_cube["cube_ancestry"], value_entry],
            cube_value=4, cube_literal=exact_literals[4],
            exhaustive_value_literals=exact_literals[1::3],
        )
        manifest.write_text(json.dumps(value_cube), encoding="utf-8")
        assert validate_symbolic_manifest(manifest, cnf, verifier) == value_cube
        next_exact_literals = [mapping[((0, 2), 2, phase)]
                               for phase in range(12)]
        next_residue_entry = {
            "anchor": "tau[(0,2),2]", "orphan": [0, 2],
            "component": 2, "residue_modulus": 3, "residue": 2,
            "clause_literals": next_exact_literals[2::3],
            "exact_phase_literals": next_exact_literals,
        }
        nested_residue_cube = dict(
            value_cube,
            scope=value_cube["scope"] + " AND tau[(0,2),2]%3=2",
            cube_anchor="tau[(0,2),2]",
            cube_ancestry=[*value_cube["cube_ancestry"],
                           next_residue_entry],
            cube_residue_modulus=3, cube_residue=2,
            cube_clause_literals=next_exact_literals[2::3],
            exact_phase_literals=next_exact_literals,
            exact_one_hot_verified=True,
            exact_pairwise_exclusions_verified=True,
        )
        manifest.write_text(json.dumps(nested_residue_cube), encoding="utf-8")
        assert validate_symbolic_manifest(
            manifest, cnf, verifier) == nested_residue_cube
        malformed_nested = dict(
            nested_residue_cube,
            cube_clause_literals=next_exact_literals[1::3])
        manifest.write_text(json.dumps(malformed_nested), encoding="utf-8")
        try:
            validate_symbolic_manifest(manifest, cnf, verifier)
            raise AssertionError("malformed nested residue cube accepted")
        except ValueError as exc:
            assert "unexpected symbolic manifest scope" in str(exc)
        malformed_value = dict(value_cube, cube_literal=exact_literals[7])
        manifest.write_text(json.dumps(malformed_value), encoding="utf-8")
        try:
            validate_symbolic_manifest(manifest, cnf, verifier)
            raise AssertionError("malformed exact-value cube accepted")
        except ValueError as exc:
            assert "unexpected symbolic manifest scope" in str(exc)
        malformed_residue = dict(residue_cube, cube_clause_literals=
                                 exact_literals[2::3])
        manifest.write_text(json.dumps(malformed_residue), encoding="utf-8")
        try:
            validate_symbolic_manifest(manifest, cnf, verifier)
            raise AssertionError("malformed residue cube accepted")
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
