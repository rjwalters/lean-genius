#!/usr/bin/env python3
"""Export the exact 78-row profile-2 reciprocal-entry inventory.

This mirrors ``oneHighProfileTwoReciprocalEntryInventoryTables`` from
``Erdos85OneHighProfileTwoReciprocalInventoryTerminal.lean``:

* profile is ``2`` (AABB),
* the cross-miss capacity predicate holds, and
* the relevant table coordinate ``(0, 2)`` is exactly ``2``.

The default TSV output is a targeted certificate manifest.
``--jsonl-output`` writes original authoritative inventory records, while
``--queue-output`` writes the legacy table-dictionary JSONL consumed directly
by ``queue_v2.py`` and ``sweep_worker.py``.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from filter_h1_capacity_inventory import (
    TABLE_PAIRS,
    has_cross_miss_capacity,
    read_latest_results,
    worker_tag,
)


PROFILE = 2
RECIPROCAL_PAIR = (0, 2)
RECIPROCAL_VALUE = 2
EXPECTED_COUNT = 78
PAIR_INDEX = TABLE_PAIRS.index(RECIPROCAL_PAIR)


def main() -> None:
    script = Path(__file__).resolve()
    repo = script.parents[4]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--inventory",
        type=Path,
        default=repo / "proofs/Proofs/Certificates/h1_orbit_inventory.compact",
    )
    parser.add_argument("--results", type=Path)
    parser.add_argument(
        "--jsonl-inventory",
        type=Path,
        help="authoritative JSONL inventory used with --jsonl-output",
    )
    parser.add_argument(
        "--jsonl-output",
        type=Path,
        help="write selected authoritative JSONL records to this path",
    )
    parser.add_argument(
        "--queue-output",
        type=Path,
        help="write selected table dictionaries for queue_v2.py",
    )
    parser.add_argument(
        "--tier1-jobs-output",
        type=Path,
        help="write seven-field jobs TSV for run_h1_v2_tier1.py",
    )
    parser.add_argument(
        "--solver-output-dir",
        type=Path,
        help="verified queue_v2 output used with --tier1-jobs-output",
    )
    parser.add_argument("--summary-only", action="store_true")
    args = parser.parse_args()

    if bool(args.jsonl_inventory) != bool(args.jsonl_output):
        parser.error("--jsonl-inventory and --jsonl-output must be supplied together")
    if bool(args.tier1_jobs_output) != bool(args.solver_output_dir):
        parser.error(
            "--tier1-jobs-output and --solver-output-dir must be supplied together"
        )

    latest = read_latest_results(args.results)
    selected: list[tuple[str, tuple[int, ...], str]] = []
    for line_number, raw in enumerate(args.inventory.read_text().splitlines(), 1):
        fields = raw.split()
        if not fields:
            continue
        profile, *raw_values = map(int, fields)
        values = tuple(raw_values)
        if profile not in range(5) or len(values) != len(TABLE_PAIRS):
            raise ValueError(f"{args.inventory}:{line_number}: malformed inventory row")
        if (
            profile == PROFILE
            and has_cross_miss_capacity(values)
            and values[PAIR_INDEX] == RECIPROCAL_VALUE
        ):
            tag = worker_tag(values)
            selected.append((tag, values, latest.get(tag, "MISSING")))

    if len(selected) != EXPECTED_COUNT:
        raise ValueError(
            f"expected {EXPECTED_COUNT} reciprocal rows, found {len(selected)}"
        )
    tags = {tag for tag, _, _ in selected}
    if len(tags) != EXPECTED_COUNT:
        raise ValueError("selected reciprocal rows do not have unique worker tags")

    if args.jsonl_inventory:
        records: dict[str, str] = {}
        for line_number, raw in enumerate(
            args.jsonl_inventory.read_text().splitlines(), 1
        ):
            if not raw:
                continue
            record = json.loads(raw)
            tag = record.get("orbit")
            if tag in tags:
                if tag in records:
                    raise ValueError(
                        f"{args.jsonl_inventory}:{line_number}: duplicate orbit {tag}"
                    )
                records[tag] = raw
        missing = tags - records.keys()
        if missing:
            raise ValueError(
                f"JSONL inventory is missing selected tags: {sorted(missing)[:5]}"
            )
        args.jsonl_output.write_text(
            "".join(records[tag] + "\n" for tag, _, _ in selected)
        )

    if args.queue_output:
        queue_lines = []
        for expected_tag, values, _ in selected:
            table = {
                str(pair): value
                for pair, value in zip(TABLE_PAIRS, values, strict=True)
                if value != 0
            }
            line = json.dumps(table, separators=(",", ":"))
            parsed_values = tuple(
                int(json.loads(line).get(str(pair), 0)) for pair in TABLE_PAIRS
            )
            if worker_tag(parsed_values) != expected_tag:
                raise ValueError(f"queue serialization changed tag {expected_tag}")
            queue_lines.append(line)
        args.queue_output.write_text("".join(line + "\n" for line in queue_lines))

    if args.tier1_jobs_output:
        table_dir = args.tier1_jobs_output.parent / "tables"
        table_dir.mkdir(parents=True, exist_ok=True)
        job_lines = []
        for tag, values, _ in selected:
            cnf = args.solver_output_dir / f"{tag}.v2.cnf"
            drat_gz = args.solver_output_dir / f"{tag}.v2.drat.gz"
            verdict = args.solver_output_dir / f"{tag}.v2.verdict"
            if not cnf.is_file() or not drat_gz.is_file() or not verdict.is_file():
                raise ValueError(f"solver artifacts are incomplete for {tag}")
            verdict_fields = verdict.read_text().split()
            if (
                len(verdict_fields) < 6
                or verdict_fields[0] != tag
                or verdict_fields[1] != "UNSAT"
                or verdict_fields[3] != "drat:VERIFIED"
                or verdict_fields[4] != "mode:MONO"
                or verdict_fields[5] != "arm:v2"
            ):
                raise ValueError(f"solver verdict is not verified MONO v2 for {tag}")
            table_path = table_dir / f"{tag}.table"
            table_record = [
                [[pair[0], pair[1]], value]
                for pair, value in zip(TABLE_PAIRS, values, strict=True)
                if value != 0
            ]
            table_path.write_text(json.dumps(table_record) + "\n")
            job_lines.append(
                "\t".join(
                    (
                        tag,
                        str(PROFILE),
                        "AABB",
                        "MONO",
                        str(table_path),
                        str(cnf),
                        str(drat_gz),
                    )
                )
            )
        args.tier1_jobs_output.write_text(
            "".join(line + "\n" for line in job_lines)
        )

    if not args.summary_only:
        print("profile\ttag\tlatest_status\ttable_values")
        for tag, values, status in selected:
            print(f"{PROFILE}\t{tag}\t{status}\t{' '.join(map(str, values))}")

    accepted = sum(status == "LEAN_ACCEPTED" for _, _, status in selected)
    print(
        f"# profile={PROFILE} pair={RECIPROCAL_PAIR} value={RECIPROCAL_VALUE} "
        f"selected={len(selected)} accepted={accepted} pending={len(selected) - accepted}"
    )


if __name__ == "__main__":
    main()
