#!/usr/bin/env python3
"""Split an exact 12-phase symbolic domain into three residue classes."""

import argparse
import hashlib
import itertools
import json
from pathlib import Path

from split_symbolic_phase_anchor import (
    inherited_ancestry, parse_header, sha256_file,
)
from verify_symbolic_hlift_assignment import phase_variable_map


def expected_clause_sha256(parent, variables, clauses, literals):
    digest = hashlib.sha256()
    digest.update(f"p cnf {variables} {clauses + 1}\n".encode())
    with open(parent, "rb") as stream:
        stream.readline()
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    digest.update((" ".join(map(str, literals)) + " 0\n").encode())
    return digest.hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest", type=Path)
    parser.add_argument("cnf", type=Path)
    parser.add_argument("output_dir", type=Path)
    parser.add_argument("--anchor", nargs=3, type=int, required=True,
                        metavar=("OMIT", "COPY", "COMPONENT"))
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--reuse-existing-cnfs", action="store_true")
    args = parser.parse_args()

    doc = json.loads(args.manifest.read_text())
    if not doc.get("options", {}).get("phase_symmetry"):
        raise ValueError("phase-symmetry option is required")
    actual_sha = sha256_file(args.cnf)
    if actual_sha != doc["sha256"]:
        raise ValueError(f"parent CNF hash mismatch: {actual_sha}")
    with open(args.cnf, "rb") as stream:
        variables, clauses = parse_header(stream.readline())
    if (variables, clauses) != (doc["vars"], doc["clauses"]):
        raise ValueError("parent CNF header/manifest mismatch")

    mapping, _last_phase = phase_variable_map()
    omit, copy, component = args.anchor
    if (omit not in range(4) or copy not in range(4) or
            component not in range(4) or component == omit):
        raise ValueError(f"invalid phase anchor: {args.anchor}")
    orphan = (omit, copy)
    literals = [mapping[orphan, component, phase] for phase in range(12)]
    residue_literals = [[literals[phase] for phase in range(residue, 12, 3)]
                        for residue in range(3)]

    one_hot = (" ".join(map(str, literals)) + " 0").encode()
    exclusions = {
        (f"-{left} -{right} 0").encode()
        for left, right in itertools.combinations(literals, 2)
    }
    required = {one_hot, *exclusions}
    found = set()
    with open(args.cnf, "rb") as stream:
        stream.readline()
        for line in stream:
            clause = line.strip()
            if clause in required:
                found.add(clause)
                if found == required:
                    break
    if one_hot not in found:
        raise ValueError("parent lacks exact 12-phase one-hot clause")
    missing = exclusions - found
    if missing:
        raise ValueError("parent lacks exact phase exclusion clause(s): " +
                         ", ".join(sorted(x.decode() for x in missing)))

    anchor_name = f"tau[({omit},{copy}),{component}]"
    anchor_tag = f"o{omit}c{copy}_e{component}"
    summary = {
        "parent_sha256": actual_sha,
        "parent_header": [variables, clauses],
        "anchor": anchor_name,
        "exact_phase_literals": literals,
        "residue_literals": residue_literals,
        "exact_one_hot_verified": True,
        "exact_pairwise_exclusions_verified": True,
        "residue_partition_verified": True,
    }
    if args.dry_run:
        print(json.dumps(summary, indent=1))
        return

    parent_ancestry = inherited_ancestry(doc, mapping)
    args.output_dir.mkdir(parents=True, exist_ok=True)
    cube_docs = []
    for residue, branch_literals in enumerate(residue_literals):
        stem = f"{args.cnf.stem}.residue_{anchor_tag}_r{residue}"
        output = args.output_dir / f"{stem}.cnf"
        expected_sha = expected_clause_sha256(
            args.cnf, variables, clauses, branch_literals)
        if args.reuse_existing_cnfs:
            if not output.is_file() or sha256_file(output) != expected_sha:
                raise ValueError(f"existing child CNF mismatch: {output}")
        else:
            with open(args.cnf, "rb") as source, open(output, "wb") as target:
                source.readline()
                target.write(f"p cnf {variables} {clauses + 1}\n".encode())
                for line in source:
                    target.write(line)
                target.write((" ".join(map(str, branch_literals)) +
                              " 0\n").encode())
            if sha256_file(output) != expected_sha:
                raise RuntimeError("written child CNF hash mismatch")
        ancestry_entry = {
            "anchor": anchor_name,
            "orphan": [omit, copy],
            "component": component,
            "residue_modulus": 3,
            "residue": residue,
            "clause_literals": branch_literals,
            "exact_phase_literals": literals,
        }
        rule_counts = dict(doc["rule_counts"])
        index = 1 + sum(name.startswith("phase_residue_cube_clause")
                        for name in rule_counts)
        rule_name = ("phase_residue_cube_clause" if index == 1 else
                     f"phase_residue_cube_clause_{index}")
        rule_counts[rule_name] = 1
        cube = {
            "scope": doc["scope"] + f" AND {anchor_name}%3={residue}",
            "parent_manifest": str(args.manifest),
            "parent_manifest_sha256": sha256_file(args.manifest),
            "parent_cnf": str(args.cnf),
            "parent_cnf_sha256": actual_sha,
            "vars": variables,
            "clauses": clauses + 1,
            "sha256": expected_sha,
            "encoder_sha256": doc["encoder_sha256"],
            "sat_verifier_sha256": doc["sat_verifier_sha256"],
            "options": doc.get("options", {}),
            "rule_counts": rule_counts,
            "cube_anchor": anchor_name,
            "cube_ancestry": [*parent_ancestry, ancestry_entry],
            "cube_residue_modulus": 3,
            "cube_residue": residue,
            "cube_clause_literals": branch_literals,
            "exact_phase_literals": literals,
            "exact_one_hot_verified": True,
            "exact_pairwise_exclusions_verified": True,
            "cube_partition_verified": True,
        }
        cube_manifest = args.output_dir / f"{stem}.manifest.json"
        cube_manifest.write_text(json.dumps(cube, indent=1) + "\n")
        cube_docs.append({"cnf": str(output), "manifest": str(cube_manifest),
                          "sha256": expected_sha})
    summary["cubes"] = cube_docs
    print(json.dumps(summary, indent=1))


if __name__ == "__main__":
    main()
