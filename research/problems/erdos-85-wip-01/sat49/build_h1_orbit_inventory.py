#!/usr/bin/env python3
"""Reconstruct the durable h=1 orbit inventory from queue shards/verdicts.

The remote sweep tree contains overlapping JSONL shards and verdict files.
This tool canonicalizes their table payloads exactly as the workers hash them,
deduplicates by the 16-hex orbit tag, checks profile row sums, and writes one
stable JSONL inventory.  It exits nonzero while any authoritative enumerator
count is missing, making partial artifact recovery explicit.
"""

import argparse
import glob
import hashlib
import json
import os
import re
import sys


EXPECTED = {"AAAA": 842, "AAAB": 2700, "AABB": 4801,
            "ABBB": 3662, "BBBB": 1536}
VERDICT_TABLE = re.compile(r"profile:(\w+).*?table:(\[.*\])")


def tuple_key(text):
    return tuple(map(int, text.strip("()").split(",")))


def normalize_table(payload):
    if isinstance(payload, dict):
        items = [(tuple_key(key), int(value)) for key, value in payload.items()]
    else:
        items = [(tuple(map(int, key)), int(value)) for key, value in payload]
    return sorted((key, value) for key, value in items if value)


def orbit_tag(items):
    # This is byte-for-byte the queue_v2.py / sweep_worker.py tag convention.
    return hashlib.sha1(json.dumps(items).encode()).hexdigest()[:16]


def profile_from_rows(items):
    rows = [0] * 8
    for (left, right), value in items:
        rows[left] += value
        rows[right] += value
    word = []
    for pair in range(4):
        row_pair = (rows[2 * pair], rows[2 * pair + 1])
        if row_pair == (2, 4):
            word.append("A")
        elif row_pair == (4, 4):
            word.append("B")
        else:
            raise ValueError(f"invalid row pair {pair}: {row_pair}; rows={rows}")
    return "".join(word), rows


def insert(found, profile, payload, source):
    items = normalize_table(payload)
    inferred, rows = profile_from_rows(items)
    if profile not in (None, "?", inferred):
        raise ValueError(f"profile mismatch {profile} != {inferred} in {source}")
    tag = orbit_tag(items)
    record = {"orbit": tag, "profile": inferred, "rows": rows,
              "table": [[[a, b], value] for (a, b), value in items]}
    old = found.get(tag)
    if old is not None and old != record:
        raise ValueError(f"orbit-tag collision at {tag}: {source}")
    found[tag] = record


def collect(root):
    found = {}
    for path in glob.glob(os.path.join(root, "**", "*.jsonl"), recursive=True):
        with open(path, encoding="utf-8") as handle:
            for line_number, line in enumerate(handle, 1):
                if not line.strip():
                    continue
                data = json.loads(line)
                payload = data.get("table", data)
                insert(found, data.get("profile"), payload,
                       f"{path}:{line_number}")
    for path in glob.glob(os.path.join(root, "**", "*.v2.verdict"), recursive=True):
        text = open(path, encoding="utf-8").read()
        match = VERDICT_TABLE.search(text)
        if match:
            insert(found, match.group(1), json.loads(match.group(2)), path)
    return found


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("root", help="remote-sweeps artifact directory")
    parser.add_argument("output", help="stable deduplicated JSONL output")
    parser.add_argument("--allow-partial", action="store_true")
    args = parser.parse_args()
    found = collect(args.root)
    records = sorted(found.values(), key=lambda record: record["orbit"])
    with open(args.output, "w", encoding="utf-8") as handle:
        for record in records:
            handle.write(json.dumps(record, separators=(",", ":"),
                                    sort_keys=True) + "\n")
    actual = {profile: 0 for profile in EXPECTED}
    for record in records:
        actual[record["profile"]] += 1
    for profile in EXPECTED:
        missing = EXPECTED[profile] - actual[profile]
        print(f"{profile}\tactual={actual[profile]}\texpected={EXPECTED[profile]}"
              f"\tmissing={missing}")
    print(f"TOTAL\tactual={len(records)}\texpected={sum(EXPECTED.values())}"
          f"\tmissing={sum(EXPECTED.values()) - len(records)}")
    complete = actual == EXPECTED
    return 0 if complete or args.allow_partial else 1


if __name__ == "__main__":
    sys.exit(main())
