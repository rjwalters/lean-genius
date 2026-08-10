#!/usr/bin/env python3
"""Aggregate three certified phase cubes into one parent-level result.

This consumer does not trust filenames or an UNSAT status line.  It checks
the exhaustive cube partition provenance, every CNF hash, and the three
DRAT-verification reports before emitting a parent-level verdict.
"""

import argparse
import hashlib
from itertools import combinations
import json
from pathlib import Path

from run_hlift_orbit_signal import sha256_file
from verify_symbolic_hlift_assignment import phase_variable_map


VERIFIED = "SYMBOLIC_CLASS_UNSAT_DRAT_VERIFIED"


def load(path):
    with open(path, encoding="utf-8") as stream:
        return json.load(stream)


def verified_log(path):
    with open(path, encoding="utf-8", errors="replace") as stream:
        return any(line.strip() == "s VERIFIED" for line in stream)


def require_hash(path, expected, label):
    path = Path(path).resolve()
    if not path.is_file() or sha256_file(path) != expected:
        raise ValueError(f"{label} hash mismatch: {path}")
    return path


def require_exact_command(command, cnf, proof, label):
    """Check that recorded proof commands consumed the audited artifacts."""
    if not isinstance(command, list) or len(command) != 3:
        raise ValueError(f"bad {label} command")
    if Path(command[1]).resolve() != cnf or Path(command[2]).resolve() != proof:
        raise ValueError(f"{label} command artifact mismatch")


def expected_cube_hashes(parent_cnf, literals):
    """Hash the exact parent-plus-unit transformations in one parent scan."""
    with open(parent_cnf, "rb") as stream:
        header = stream.readline().decode().split()
        if len(header) != 4 or header[:2] != ["p", "cnf"]:
            raise ValueError("bad parent CNF header")
        variables, clauses = map(int, header[2:])
        digests = [hashlib.sha256() for _ in literals]
        for digest in digests:
            digest.update(f"p cnf {variables} {clauses + 1}\n".encode())
        required = {
            (" ".join(map(str, literals)) + " 0").encode(),
            *(f"-{left} -{right} 0".encode()
              for left, right in combinations(literals, 2)),
        }
        found = set()
        for line in stream:
            for digest in digests:
                digest.update(line)
            if line.strip() in required:
                found.add(line.strip())
        if found != required:
            raise ValueError("parent CNF does not contain the exact anchor partition")
    for digest, literal in zip(digests, literals):
        digest.update(f"{literal} 0\n".encode())
    return [digest.hexdigest() for digest in digests]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("parent_manifest", type=Path)
    parser.add_argument("cube_dir", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--anchor", nargs=3, type=int,
                        metavar=("OMIT", "COPY", "COMPONENT"),
                        default=(0, 0, 2))
    args = parser.parse_args()

    parent_manifest = args.parent_manifest.resolve()
    parent = load(parent_manifest)
    parent_manifest_sha = sha256_file(parent_manifest)
    parent_cnf = parent_manifest.with_suffix("").with_suffix(".cnf")
    require_hash(parent_cnf, parent["sha256"], "parent CNF")
    omit, copy, component = args.anchor
    mapping, _ = phase_variable_map()
    try:
        anchor_literals = [mapping[((omit, copy), component, phase)]
                           for phase in range(3)]
    except KeyError as exc:
        raise ValueError(f"invalid phase anchor: {args.anchor}") from exc
    anchor_name = f"tau[({omit},{copy}),{component}]"
    anchor_tag = f"o{omit}c{copy}_e{component}"
    expected_hashes = expected_cube_hashes(parent_cnf, anchor_literals)
    manifests = sorted(args.cube_dir.glob(
        f"*.anchor_{anchor_tag}_p*.manifest.json"))
    if len(manifests) != 3:
        raise ValueError(f"expected exactly three cube manifests, got {len(manifests)}")

    cubes = {}
    for manifest_path in manifests:
        cube = load(manifest_path)
        phase = cube.get("cube_phase")
        if phase not in (0, 1, 2) or phase in cubes:
            raise ValueError(f"bad or duplicate cube phase: {phase!r}")
        if cube.get("parent_manifest_sha256") != parent_manifest_sha:
            raise ValueError(f"parent manifest provenance mismatch at phase {phase}")
        if cube.get("parent_cnf_sha256") != parent.get("sha256"):
            raise ValueError(f"parent CNF provenance mismatch at phase {phase}")
        if cube.get("scope") != parent["scope"] + f" AND {anchor_name}={phase}":
            raise ValueError(f"cube scope mismatch at phase {phase}")
        if not (cube.get("exhaustive_clause_verified") and
                cube.get("mutual_exclusion_clauses_verified") and
                cube.get("cube_partition_verified")):
            raise ValueError(f"unverified cube partition at phase {phase}")
        cube_literals = cube.get("exhaustive_anchor_literals")
        if (cube_literals != anchor_literals or
                cube.get("cube_literal") != anchor_literals[phase]):
            raise ValueError(f"anchor literal mismatch at phase {phase}")
        if cube.get("sha256") != expected_hashes[phase]:
            raise ValueError(f"cube is not the exact parent-plus-unit transform at phase {phase}")
        cnf = require_hash(manifest_path.with_suffix("").with_suffix(".cnf"),
                           cube["sha256"], f"phase {phase} CNF")
        cubes[phase] = (manifest_path, cube, cnf)

    certificates = {}
    for cert_path in args.cube_dir.glob("**/certificate.json"):
        cert = load(cert_path)
        cnf_sha = cert.get("cnf_sha256")
        matches = [phase for phase, (_, cube, _) in cubes.items()
                   if cube["sha256"] == cnf_sha]
        if len(matches) != 1:
            raise ValueError(f"certificate has unknown cube CNF: {cert_path}")
        phase = matches[0]
        if phase in certificates:
            raise ValueError(f"duplicate certificate for phase {phase}")
        manifest_path, _cube, cnf = cubes[phase]
        if cert.get("verdict") != VERIFIED:
            raise ValueError(f"certificate is not DRAT-verified at phase {phase}")
        if cert.get("manifest_sha256") != sha256_file(manifest_path):
            raise ValueError(f"cube manifest provenance mismatch at phase {phase}")
        if Path(cert.get("cnf", "")).resolve() != cnf:
            raise ValueError(f"certificate CNF path mismatch at phase {phase}")
        proof = require_hash(cert["proof"], cert["proof_sha256"],
                             f"phase {phase} proof")
        require_exact_command(cert.get("solver_command"), cnf, proof,
                              f"phase {phase} solver")
        require_exact_command(cert.get("drat_trim_command"), cnf, proof,
                              f"phase {phase} drat-trim")
        log_path = cert_path.parent / "drat-trim.log"
        require_hash(log_path, cert["drat_trim_log_sha256"],
                     f"phase {phase} drat-trim log")
        if cert.get("drat_trim_exit") != 0 or not verified_log(log_path):
            raise ValueError(f"DRAT verification evidence failed at phase {phase}")
        certificates[phase] = cert_path

    missing = sorted(set(range(3)) - set(certificates))
    if missing:
        raise ValueError(f"missing verified certificate phase(s): {missing}")
    report = {
        "verdict": "SYMBOLIC_PARENT_UNSAT_BY_EXHAUSTIVE_DRAT_VERIFIED_CUBES",
        "scope": parent["scope"],
        "parent_manifest": str(parent_manifest),
        "parent_manifest_sha256": parent_manifest_sha,
        "parent_cnf": str(parent_cnf),
        "parent_cnf_sha256": parent["sha256"],
        "anchor": anchor_name,
        "anchor_literals": anchor_literals,
        "cube_partition_verified": True,
        "cube_certificates": [
            {"phase": phase, "certificate": str(certificates[phase]),
             "certificate_sha256": sha256_file(certificates[phase])}
            for phase in range(3)
        ],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=1) + "\n")
    print(report["verdict"], args.output)


if __name__ == "__main__":
    main()
