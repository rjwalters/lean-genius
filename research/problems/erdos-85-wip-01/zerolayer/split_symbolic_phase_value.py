#!/usr/bin/env python3
"""Split a certified phase-residue cube into its four exact values."""

import argparse
import itertools
import json
from pathlib import Path

from split_symbolic_phase_anchor import (
    expected_cube_sha256, inherited_ancestry, parse_header, sha256_file,
)
from verify_symbolic_hlift_assignment import phase_variable_map


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
    actual_sha = sha256_file(args.cnf)
    if actual_sha != doc["sha256"]:
        raise ValueError(f"parent CNF hash mismatch: {actual_sha}")
    with open(args.cnf, "rb") as stream:
        variables, clauses = parse_header(stream.readline())
    if (variables, clauses) != (doc["vars"], doc["clauses"]):
        raise ValueError("parent CNF header/manifest mismatch")

    omit, copy, component = args.anchor
    if (omit not in range(4) or copy not in range(4) or
            component not in range(4) or component == omit):
        raise ValueError(f"invalid phase anchor: {args.anchor}")
    anchor_name = f"tau[({omit},{copy}),{component}]"
    if (doc.get("cube_anchor") != anchor_name or
            doc.get("cube_residue_modulus") != 3 or
            doc.get("cube_residue") not in range(3) or
            not doc.get("cube_partition_verified") or
            not doc.get("exact_one_hot_verified") or
            not doc.get("exact_pairwise_exclusions_verified")):
        raise ValueError("parent is not a certified residue cube at this anchor")

    mapping, _last_phase = phase_variable_map()
    orphan = (omit, copy)
    exact_literals = [mapping[orphan, component, phase]
                      for phase in range(12)]
    residue = doc["cube_residue"]
    branch_literals = exact_literals[residue::3]
    if (doc.get("exact_phase_literals") != exact_literals or
            doc.get("cube_clause_literals") != branch_literals):
        raise ValueError("parent residue literals do not match exact mapping")

    residue_clause = (" ".join(map(str, branch_literals)) + " 0").encode()
    one_hot = (" ".join(map(str, exact_literals)) + " 0").encode()
    exclusions = {
        (f"-{left} -{right} 0").encode()
        for left, right in itertools.combinations(exact_literals, 2)
    }
    required = {residue_clause, one_hot, *exclusions}
    found = set()
    with open(args.cnf, "rb") as stream:
        stream.readline()
        for line in stream:
            clause = line.strip()
            if clause in required:
                found.add(clause)
                if found == required:
                    break
    if residue_clause not in found:
        raise ValueError("parent lacks exact residue clause")
    if one_hot not in found or exclusions - found:
        raise ValueError("parent lacks exact 12-phase one-hot constraints")

    summary = {
        "parent_sha256": actual_sha,
        "parent_header": [variables, clauses],
        "anchor": anchor_name,
        "residue": residue,
        "value_literals": branch_literals,
        "exact_value_partition_verified": True,
    }
    if args.dry_run:
        print(json.dumps(summary, indent=1))
        return

    parent_ancestry = inherited_ancestry(doc, mapping)
    args.output_dir.mkdir(parents=True, exist_ok=True)
    cube_docs = []
    anchor_tag = f"o{omit}c{copy}_e{component}"
    for literal in branch_literals:
        value = exact_literals.index(literal)
        stem = f"{args.cnf.stem}.value_{anchor_tag}_v{value}"
        output = args.output_dir / f"{stem}.cnf"
        expected_sha = expected_cube_sha256(
            args.cnf, variables, clauses, literal)
        if args.reuse_existing_cnfs:
            if not output.is_file() or sha256_file(output) != expected_sha:
                raise ValueError(f"existing child CNF mismatch: {output}")
        else:
            with open(args.cnf, "rb") as source, open(output, "wb") as target:
                source.readline()
                target.write(f"p cnf {variables} {clauses + 1}\n".encode())
                for line in source:
                    target.write(line)
                target.write(f"{literal} 0\n".encode())
            if sha256_file(output) != expected_sha:
                raise RuntimeError("written child CNF hash mismatch")
        ancestry_entry = {
            "anchor": anchor_name,
            "orphan": [omit, copy],
            "component": component,
            "value": value,
            "literal": literal,
            "exhaustive_value_literals": branch_literals,
        }
        rule_counts = dict(doc["rule_counts"])
        index = 1 + sum(name.startswith("phase_value_cube_unit")
                        for name in rule_counts)
        rule_name = ("phase_value_cube_unit" if index == 1 else
                     f"phase_value_cube_unit_{index}")
        rule_counts[rule_name] = 1
        cube = {
            "scope": doc["scope"] + f" AND {anchor_name}={value}",
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
            "cube_value": value,
            "cube_literal": literal,
            "exhaustive_value_literals": branch_literals,
            "cube_partition_verified": True,
        }
        cube_manifest = args.output_dir / f"{stem}.manifest.json"
        cube_manifest.write_text(json.dumps(cube, indent=1) + "\n")
        cube_docs.append({"value": value, "cnf": str(output),
                          "manifest": str(cube_manifest),
                          "sha256": expected_sha})
    summary["cubes"] = cube_docs
    print(json.dumps(summary, indent=1))


if __name__ == "__main__":
    main()
