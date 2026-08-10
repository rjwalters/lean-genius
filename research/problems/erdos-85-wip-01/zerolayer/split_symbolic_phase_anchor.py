#!/usr/bin/env python3
"""Split a phase-symmetric symbolic CNF into three exhaustive anchor cubes.

This prepares signal/certificate subinstances without changing the parent.
The default anchor tau[(0,0),2] is constrained by the encoder to phases
0,1,2, so the three unit cubes are exhaustive and mutually exclusive.
"""

import argparse
import hashlib
import json
from pathlib import Path

from verify_symbolic_hlift_assignment import phase_variable_map


def sha256_file(path):
    digest = hashlib.sha256()
    with open(path, "rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def parse_header(line):
    fields = line.decode().strip().split()
    if len(fields) != 4 or fields[:2] != ["p", "cnf"]:
        raise ValueError(f"bad CNF header: {line!r}")
    return int(fields[2]), int(fields[3])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest", type=Path)
    parser.add_argument("cnf", type=Path)
    parser.add_argument("output_dir", type=Path)
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()

    doc = json.loads(args.manifest.read_text())
    if not doc.get("options", {}).get("phase_symmetry"):
        raise ValueError("phase-symmetry option is required for a 3-way cube")
    actual_sha = sha256_file(args.cnf)
    if actual_sha != doc["sha256"]:
        raise ValueError(f"parent CNF hash mismatch: {actual_sha}")
    with open(args.cnf, "rb") as stream:
        header = stream.readline()
    variables, clauses = parse_header(header)
    if (variables, clauses) != (doc["vars"], doc["clauses"]):
        raise ValueError("parent CNF header/manifest mismatch")

    mapping, _last_phase = phase_variable_map()
    anchor = ((0, 0), 2)
    literals = [mapping[anchor[0], anchor[1], phase] for phase in range(3)]
    exhaustive_clause = (" ".join(map(str, literals)) + " 0").encode()
    found_exhaustive = False
    with open(args.cnf, "rb") as stream:
        stream.readline()
        for line in stream:
            if line.strip() == exhaustive_clause:
                found_exhaustive = True
                break
    if not found_exhaustive:
        raise ValueError("parent lacks the exact three-phase anchor clause")

    summary = {"parent_sha256": actual_sha, "parent_header": [variables, clauses],
               "anchor": "tau[(0,0),2]", "literals": literals,
               "exhaustive_clause_verified": True}
    if args.dry_run:
        print(json.dumps(summary, indent=1))
        return

    args.output_dir.mkdir(parents=True, exist_ok=True)
    cube_docs = []
    for phase, literal in enumerate(literals):
        stem = f"{args.cnf.stem}.anchor_o0c0_e2_p{phase}"
        output = args.output_dir / f"{stem}.cnf"
        with open(args.cnf, "rb") as source, open(output, "wb") as target:
            source.readline()
            target.write(f"p cnf {variables} {clauses + 1}\n".encode())
            for line in source:
                target.write(line)
            target.write(f"{literal} 0\n".encode())
        cube = {
            "scope": doc["scope"] + f" AND tau[(0,0),2]={phase}",
            "parent_manifest": str(args.manifest),
            "parent_manifest_sha256": sha256_file(args.manifest),
            "parent_cnf": str(args.cnf), "parent_cnf_sha256": actual_sha,
            "vars": variables, "clauses": clauses + 1,
            "sha256": sha256_file(output), "cube_literal": literal,
            "cube_phase": phase, "exhaustive_anchor_literals": literals,
            "exhaustive_clause_verified": True,
        }
        cube_manifest = args.output_dir / f"{stem}.manifest.json"
        cube_manifest.write_text(json.dumps(cube, indent=1) + "\n")
        cube_docs.append({"cnf": str(output), "manifest": str(cube_manifest),
                          "sha256": cube["sha256"]})
    summary["cubes"] = cube_docs
    print(json.dumps(summary, indent=1))


if __name__ == "__main__":
    main()
