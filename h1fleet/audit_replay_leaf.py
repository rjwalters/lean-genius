#!/usr/bin/env python3
"""Extract one literal Lean ``#print axioms`` result from a worker log."""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

from replay_common import ReplayError, atomic_write, canonical_json


def source_scan(path: Path) -> None:
    source = path.read_text()
    forbidden = re.compile(r"(?m)(?<![A-Za-z0-9_])(sorry|admit)(?![A-Za-z0-9_])")
    if forbidden.search(source):
        raise ReplayError("source scan found sorry or admit")
    if "#print axioms" not in source:
        raise ReplayError("source lacks literal #print axioms command")


def compiler_stdout(log: Path) -> str:
    outputs = []
    for line_number, line in enumerate(log.read_text().splitlines(), 1):
        try:
            record = json.loads(line)
        except json.JSONDecodeError as error:
            raise ReplayError(f"worker log line {line_number} is not JSON") from error
        if not isinstance(record, dict):
            raise ReplayError(f"worker log line {line_number} is not an object")
        argv = record.get("argv")
        if isinstance(argv, list) and record.get("returncode") == 0:
            outputs.append(str(record.get("stdout", "")) + "\n" + str(record.get("stderr", "")))
    if not outputs:
        raise ReplayError("worker log contains no successful command output")
    return "\n".join(outputs)


def parse_axioms(output: str, theorem: str) -> list[str]:
    # Lean 4.31 prints: `axioms Qualified.name : [a, b, generated.ax_1]`.
    expression = re.compile(
        rf"(?ms)axioms\s+{re.escape(theorem)}\s*:\s*\[([^]]*)\]"
    )
    matches = expression.findall(output)
    if len(matches) != 1:
        raise ReplayError(
            f"expected one literal axiom report for {theorem}, found {len(matches)}"
        )
    axioms = [entry.strip() for entry in matches[0].split(",") if entry.strip()]
    if len(axioms) != len(set(axioms)):
        raise ReplayError("axiom report contains duplicates")
    if any(not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*", axiom) for axiom in axioms):
        raise ReplayError("axiom report contains an invalid declaration name")
    return axioms


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--log", type=Path, required=True)
    parser.add_argument("--theorem", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    try:
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*", args.theorem):
            raise ReplayError("invalid theorem name")
        source_scan(args.source)
        axioms = parse_axioms(compiler_stdout(args.log), args.theorem)
        receipt = {
            "schema": "erdos85-h1-replay-axiom-audit-v1",
            "theorem": args.theorem, "source_scan": "PASS",
            "sorry_ax": "sorryAx" in axioms, "axioms": axioms,
        }
        atomic_write(args.output, canonical_json(receipt))
        print(json.dumps(receipt, sort_keys=True))
        return 0
    except (OSError, ReplayError) as error:
        print(f"AXIOM_AUDIT_ERROR: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
