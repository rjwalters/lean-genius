#!/usr/bin/env python3
"""Convert the authoritative h=1 JSONL inventory to Lean's compact format.

Each output row is 25 decimal integers: the profile number (BBBB=0 through
AAAA=4), followed by the 24 upper non-mate entries in the exact nested-loop
order of `oneHighFamilyTablePairs`.  Missing sparse JSON entries are zero.
"""

import argparse
import hashlib
import json
from pathlib import Path

MATE = (1, 0, 3, 2, 5, 4, 7, 6)
EDGES = tuple((i, j) for i in range(8) for j in range(i + 1, 8)
              if j != MATE[i])
PROFILE = {"BBBB": 0, "ABBB": 1, "AABB": 2, "AAAB": 3, "AAAA": 4}
EXPECTED_COUNTS = {0: 1536, 1: 3662, 2: 4801, 3: 2700, 4: 842}
EXPECTED_INPUT_SHA256 = (
    "94e73da7116fdd9c8e396bcad5e9e8ba113257acac663e7e953e5ea5647ca1e6"
)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()

    raw = args.input.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    if digest != EXPECTED_INPUT_SHA256:
        raise SystemExit(f"unexpected input sha256: {digest}")

    rows = []
    counts = {p: 0 for p in range(5)}
    for line in raw.splitlines():
        item = json.loads(line)
        profile = PROFILE[item["profile"]]
        sparse = {(c, j): n for (c, j), n in item["table"]}
        values = [sparse.get(edge, 0) for edge in EDGES]
        if any(not 0 <= value <= 4 for value in values):
            raise SystemExit(f"out-of-range entry in orbit {item['orbit']}")
        rows.append(" ".join(map(str, [profile, *values])))
        counts[profile] += 1

    if counts != EXPECTED_COUNTS:
        raise SystemExit(f"unexpected profile counts: {counts}")
    args.output.write_text("\n".join(rows) + "\n")
    print(f"rows={len(rows)} counts={counts}")
    print(f"input_sha256={digest}")
    print(f"output_sha256={hashlib.sha256(args.output.read_bytes()).hexdigest()}")


if __name__ == "__main__":
    main()
