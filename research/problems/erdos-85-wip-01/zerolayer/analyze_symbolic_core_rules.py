#!/usr/bin/env python3
"""Map a drat-trim original-clause core back to encoder rule families.

The manifest's ``rule_counts`` are insertion ordered and cover the CNF in
encoder emission order.  ``drat-trim -c`` emits a subset of original input
clauses.  This script matches that subset as a multiset and reports how many
core clauses came from each rule-family interval.
"""

import argparse
from bisect import bisect_right
from collections import Counter
import json
from pathlib import Path


def clauses(path):
    expected = None
    seen = 0
    with open(path, "rb") as stream:
        for line in stream:
            stripped = line.strip()
            if not stripped or stripped.startswith(b"c"):
                continue
            if stripped.startswith(b"p"):
                fields = stripped.split()
                if len(fields) != 4 or fields[:2] != [b"p", b"cnf"]:
                    raise ValueError(f"bad DIMACS header in {path}")
                expected = int(fields[3])
                continue
            values = [int(field) for field in stripped.split()]
            if not values or values[-1] != 0 or 0 in values[:-1]:
                raise ValueError(f"bad clause in {path}: {stripped[:80]!r}")
            seen += 1
            # Literal order is semantically irrelevant and drat-trim need not
            # preserve it in the extracted core.
            yield tuple(sorted(values[:-1]))
    if expected is None or seen != expected:
        raise ValueError(f"DIMACS clause count mismatch in {path}: {seen} != {expected}")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest", type=Path)
    parser.add_argument("cnf", type=Path)
    parser.add_argument("core", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    manifest = json.loads(args.manifest.read_text())
    families = list(manifest["rule_counts"].items())
    endpoints = []
    total = 0
    for _name, count in families:
        total += count
        endpoints.append(total)
    if total != manifest["clauses"]:
        raise ValueError("manifest rule counts do not cover its clauses")

    needed = Counter(clauses(args.core))
    target_clauses = set(needed)
    first_family = {}
    ambiguous = set()
    core_clauses = sum(needed.values())
    counts = Counter()
    matched = 0
    for index, clause in enumerate(clauses(args.cnf)):
        if clause not in target_clauses:
            continue
        family_index = bisect_right(endpoints, index)
        if family_index == len(families):
            raise ValueError("CNF has clauses beyond manifest rule ranges")
        family = families[family_index][0]
        if clause in first_family and first_family[clause] != family:
            ambiguous.add(clause)
        else:
            first_family[clause] = family
        if needed.get(clause, 0) == 0:
            continue
        needed[clause] -= 1
        if needed[clause] == 0:
            del needed[clause]
        counts[family] += 1
        matched += 1

    if needed:
        raise ValueError(
            f"{sum(needed.values())} extracted core clauses were not in the CNF")
    report = {
        "verdict": "ORIGINAL_CLAUSE_CORE_MAPPED_TO_RULE_FAMILIES",
        "manifest": str(args.manifest.resolve()),
        "cnf": str(args.cnf.resolve()),
        "core": str(args.core.resolve()),
        "cnf_clauses": manifest["clauses"],
        "core_clauses": core_clauses,
        "matched_core_clauses": matched,
        "cross_family_duplicate_clause_shapes": len(ambiguous),
        "family_assignment_note": (
            "Duplicate clause occurrences are assigned to their earliest CNF "
            "occurrences; family counts are unique exactly when "
            "cross_family_duplicate_clause_shapes is zero."
        ),
        "families": [
            {"name": name, "cnf_clauses": size,
             "core_clauses": counts[name],
             "retained_fraction": counts[name] / size if size else 0.0}
            for name, size in families
        ],
    }
    rendered = json.dumps(report, indent=1) + "\n"
    if args.output:
        args.output.write_text(rendered)
    print(rendered, end="")


if __name__ == "__main__":
    main()
