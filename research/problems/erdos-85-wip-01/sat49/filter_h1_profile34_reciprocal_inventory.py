#!/usr/bin/env python3
"""Export the exact profile-3 or profile-4 reciprocal-entry inventory.

This mirrors the transport-stable Lean predicates:

* profile 3 (AAAB): ``table 0 2 = 2 or table 0 4 = 2`` — 9 rows;
* profile 4 (AAAA): additionally ``table 0 6 = 2`` — 46 rows.

Every selected row must also satisfy the graph-side cross-miss capacity
predicate.  The optional jobs output is a seven-field seed queue for the
Lean-exact solver; its CNF and DRAT fields are intentionally empty because
that runner emits the authoritative CNF itself.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from filter_h1_capacity_inventory import (
    TABLE_PAIRS,
    has_cross_miss_capacity,
    worker_tag,
)


CONFIG = {
    3: {"family": "AAAB", "labels": (2, 4), "expected": 9},
    4: {"family": "AAAA", "labels": (2, 4, 6), "expected": 46},
}


def main() -> None:
    script = Path(__file__).resolve()
    repo = script.parents[4]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("profile", type=int, choices=CONFIG)
    parser.add_argument(
        "--inventory",
        type=Path,
        default=repo / "proofs/Proofs/Certificates/h1_orbit_inventory.compact",
    )
    parser.add_argument("--manifest-output", type=Path)
    parser.add_argument("--queue-output", type=Path)
    parser.add_argument(
        "--lean-exact-jobs-output",
        type=Path,
        help="write seed jobs plus canonical table files for exact-CNF solving",
    )
    parser.add_argument("--summary-only", action="store_true")
    args = parser.parse_args()

    config = CONFIG[args.profile]
    label_indices = tuple(TABLE_PAIRS.index((0, label)) for label in config["labels"])
    selected: list[tuple[str, tuple[int, ...]]] = []
    for line_number, raw in enumerate(args.inventory.read_text().splitlines(), 1):
        fields = raw.split()
        if not fields:
            continue
        profile, *raw_values = map(int, fields)
        values = tuple(raw_values)
        if profile not in range(5) or len(values) != len(TABLE_PAIRS):
            raise ValueError(f"{args.inventory}:{line_number}: malformed inventory row")
        if (
            profile == args.profile
            and has_cross_miss_capacity(values)
            and any(values[index] == 2 for index in label_indices)
        ):
            selected.append((worker_tag(values), values))

    expected = config["expected"]
    if len(selected) != expected:
        raise ValueError(f"expected {expected} rows, found {len(selected)}")
    tags = [tag for tag, _ in selected]
    if len(set(tags)) != expected:
        raise ValueError("selected rows do not have unique worker tags")

    if args.manifest_output:
        args.manifest_output.parent.mkdir(parents=True, exist_ok=True)
        args.manifest_output.write_text(
            "".join(
                f"{tag}\t{args.profile}\t{config['family']}\t"
                f"{' '.join(map(str, values))}\n"
                for tag, values in selected
            )
        )

    if args.queue_output:
        args.queue_output.parent.mkdir(parents=True, exist_ok=True)
        lines = []
        for expected_tag, values in selected:
            table = {
                str(pair): value
                for pair, value in zip(TABLE_PAIRS, values, strict=True)
                if value != 0
            }
            line = json.dumps(table, separators=(",", ":"))
            decoded = json.loads(line)
            roundtrip = tuple(int(decoded.get(str(pair), 0)) for pair in TABLE_PAIRS)
            if worker_tag(roundtrip) != expected_tag:
                raise ValueError(f"queue serialization changed tag {expected_tag}")
            lines.append(line)
        args.queue_output.write_text("".join(line + "\n" for line in lines))

    if args.lean_exact_jobs_output:
        args.lean_exact_jobs_output.parent.mkdir(parents=True, exist_ok=True)
        table_dir = args.lean_exact_jobs_output.parent / "tables"
        table_dir.mkdir(parents=True, exist_ok=True)
        jobs = []
        for tag, values in selected:
            table_path = table_dir / f"{tag}.table"
            record = [
                [[pair[0], pair[1]], value]
                for pair, value in zip(TABLE_PAIRS, values, strict=True)
                if value != 0
            ]
            table_path.write_text(json.dumps(record) + "\n")
            jobs.append(
                "\t".join(
                    (
                        tag,
                        str(args.profile),
                        config["family"],
                        "MONO",
                        str(table_path),
                        "",
                        "",
                    )
                )
            )
        args.lean_exact_jobs_output.write_text(
            "".join(job + "\n" for job in jobs)
        )

    if not args.summary_only:
        print("profile\ttag\ttable_values")
        for tag, values in selected:
            print(f"{args.profile}\t{tag}\t{' '.join(map(str, values))}")
    print(
        f"# profile={args.profile} family={config['family']} "
        f"labels={config['labels']} selected={len(selected)}"
    )


if __name__ == "__main__":
    main()
