#!/usr/bin/env python3
"""Split a phase-symmetric symbolic CNF into three exhaustive anchor cubes.

This prepares signal/certificate subinstances without changing the parent.
The default anchor tau[(0,0),2] is constrained by the encoder to phases
0,1,2, so the three unit cubes are exhaustive and mutually exclusive.
"""

import argparse
import hashlib
import itertools
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


def inherited_ancestry(doc, mapping):
    """Upgrade the original top-cube manifests to explicit ancestry."""
    ancestry = doc.get("cube_ancestry")
    if ancestry:
        return ancestry
    if "cube_phase" not in doc:
        return []
    phase = doc["cube_phase"]
    anchor = ((0, 0), 2)
    literals = [mapping[anchor[0], anchor[1], value] for value in range(3)]
    suffix = f" AND tau[(0,0),2]={phase}"
    if (phase not in range(3) or doc.get("cube_literal") != literals[phase] or
            doc.get("exhaustive_anchor_literals") != literals or
            not doc.get("scope", "").endswith(suffix)):
        raise ValueError("legacy cube fields cannot be upgraded to ancestry")
    return [{
        "anchor": "tau[(0,0),2]", "orphan": [0, 0],
        "component": 2, "phase": phase, "literal": literals[phase],
        "exhaustive_anchor_literals": literals,
    }]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest", type=Path)
    parser.add_argument("cnf", type=Path)
    parser.add_argument("output_dir", type=Path)
    parser.add_argument("--anchor", nargs=3, type=int,
                        metavar=("OMIT", "COPY", "COMPONENT"),
                        default=(0, 0, 2))
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
    parent_ancestry = inherited_ancestry(doc, mapping)
    omit, copy, component = args.anchor
    anchor = ((omit, copy), component)
    if (omit not in range(4) or copy not in range(4) or
            component not in range(4) or component == omit):
        raise ValueError(f"invalid phase anchor: {args.anchor}")
    literals = [mapping[anchor[0], anchor[1], phase] for phase in range(3)]
    exhaustive_clause = (" ".join(map(str, literals)) + " 0").encode()
    exclusion_clauses = {
        (f"-{left} -{right} 0").encode()
        for left, right in itertools.combinations(literals, 2)
    }
    required_clauses = {exhaustive_clause, *exclusion_clauses}
    found_clauses = set()
    with open(args.cnf, "rb") as stream:
        stream.readline()
        for line in stream:
            clause = line.strip()
            if clause in required_clauses:
                found_clauses.add(clause)
                if found_clauses == required_clauses:
                    break
    if exhaustive_clause not in found_clauses:
        raise ValueError("parent lacks the exact three-phase anchor clause")
    missing_exclusions = exclusion_clauses - found_clauses
    if missing_exclusions:
        raise ValueError(
            "parent lacks exact pairwise anchor exclusion clause(s): "
            + ", ".join(sorted(clause.decode() for clause in missing_exclusions))
        )

    anchor_name = f"tau[({omit},{copy}),{component}]"
    anchor_tag = f"o{omit}c{copy}_e{component}"
    summary = {"parent_sha256": actual_sha, "parent_header": [variables, clauses],
               "anchor": anchor_name, "literals": literals,
               "exhaustive_clause_verified": True,
               "mutual_exclusion_clauses_verified": True,
               "cube_partition_verified": True}
    if args.dry_run:
        print(json.dumps(summary, indent=1))
        return

    args.output_dir.mkdir(parents=True, exist_ok=True)
    cube_docs = []
    for phase, literal in enumerate(literals):
        stem = f"{args.cnf.stem}.anchor_{anchor_tag}_p{phase}"
        output = args.output_dir / f"{stem}.cnf"
        with open(args.cnf, "rb") as source, open(output, "wb") as target:
            source.readline()
            target.write(f"p cnf {variables} {clauses + 1}\n".encode())
            for line in source:
                target.write(line)
            target.write(f"{literal} 0\n".encode())
        ancestry = [*parent_ancestry, {
            "anchor": anchor_name, "orphan": [omit, copy],
            "component": component, "phase": phase, "literal": literal,
            "exhaustive_anchor_literals": literals,
        }]
        unit_count = sum(name.startswith("phase_anchor_cube_unit")
                         for name in doc["rule_counts"])
        unit_name = ("phase_anchor_cube_unit" if unit_count == 0 else
                     f"phase_anchor_cube_unit_{unit_count + 1}")
        cube = {
            "scope": doc["scope"] + f" AND {anchor_name}={phase}",
            "parent_manifest": str(args.manifest),
            "parent_manifest_sha256": sha256_file(args.manifest),
            "parent_cnf": str(args.cnf), "parent_cnf_sha256": actual_sha,
            "vars": variables, "clauses": clauses + 1,
            "sha256": sha256_file(output), "cube_literal": literal,
            "encoder_sha256": doc["encoder_sha256"],
            "sat_verifier_sha256": doc["sat_verifier_sha256"],
            "options": doc.get("options", {}),
            "rule_counts": {
                **doc["rule_counts"], unit_name: 1,
            },
            "cube_anchor": anchor_name, "cube_ancestry": ancestry,
            "cube_phase": phase, "exhaustive_anchor_literals": literals,
            "exhaustive_clause_verified": True,
            "mutual_exclusion_clauses_verified": True,
            "cube_partition_verified": True,
        }
        cube_manifest = args.output_dir / f"{stem}.manifest.json"
        cube_manifest.write_text(json.dumps(cube, indent=1) + "\n")
        cube_docs.append({"cnf": str(output), "manifest": str(cube_manifest),
                          "sha256": cube["sha256"]})
    summary["cubes"] = cube_docs
    print(json.dumps(summary, indent=1))


if __name__ == "__main__":
    main()
