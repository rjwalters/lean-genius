#!/usr/bin/env python3
"""Independently validate portable H7 fleet freight before node execution."""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
from collections import Counter
from pathlib import Path, PurePosixPath

sys.dont_write_bytecode = True
import build_h7_fleet_freight as freight


QUEUE_SCHEMA = "erdos85-h7-canonical-empty-cube-adaptive-portable-queue-v1"
CANARY = "cube_F6_t14.adaptive.leaf-000"
CANARY_SHA = "29d6e4759bec52483e07ef01800037693be4510eee080cc4c5b52b70bfb1972e"
JOB_RE = re.compile(r"(cube_F[6-9]_t\d+)\.adaptive\.leaf-([01]{3})")


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def safe_relative(value: object, prefix: str | None = None) -> PurePosixPath:
    require(isinstance(value, str) and value != "", "missing relative path")
    path = PurePosixPath(value)
    require(not path.is_absolute() and ".." not in path.parts and "." not in path.parts,
            f"unsafe relative path: {value}")
    if prefix is not None:
        require(len(path.parts) == 2 and path.parts[0] == prefix,
                f"path is outside {prefix}: {value}")
    return path


def validate(root: Path, materialize: bool) -> str:
    root = root.resolve()
    inventory_path = root / "freight.json"
    inventory = json.loads(inventory_path.read_text())
    require(inventory.get("schema") == freight.SCHEMA, "freight schema mismatch")
    declared = inventory.get("files")
    require(isinstance(declared, dict), "missing freight file inventory")
    actual = {str(path.relative_to(root)) for path in root.rglob("*")
              if path.is_file() and path != inventory_path}
    require(set(declared) == actual and inventory.get("file_count") == len(actual),
            "freight file inventory differs from disk")
    for relative, expected in declared.items():
        path = safe_relative(relative)
        require(re.fullmatch(r"[0-9a-f]{64}", expected or "") is not None and
                freight.sha256(root / Path(*path.parts)) == expected,
                f"freight file hash mismatch: {relative}")

    queue = json.loads((root / "queue.json").read_text())
    require(queue.get("schema") == QUEUE_SCHEMA and
            queue.get("source_queue_sha256") == freight.QUEUE_SHA,
            "portable queue source/schema mismatch")
    require(queue.get("parent_manifest") == "parent.json" and
            queue.get("parent_manifest_sha256") == freight.PARENT_SHA and
            freight.sha256(root / "parent.json") == freight.PARENT_SHA,
            "portable parent binding mismatch")
    require(queue.get("base") == "base.cnf" and
            queue.get("base_sha256") == freight.BASE_SHA and
            freight.sha256(root / "base.cnf") == freight.BASE_SHA,
            "portable base binding mismatch")
    jobs = queue.get("jobs")
    require(queue.get("parent_count") == 29 and queue.get("leaf_count") == 232 and
            isinstance(jobs, list) and len(jobs) == 232,
            "portable queue cardinality mismatch")
    parents = Counter()
    ids = set()
    for row in jobs:
        job = row.get("id"); match = JOB_RE.fullmatch(job or "")
        require(match is not None and job not in ids, f"invalid/duplicate job id: {job}")
        ids.add(job); parents[match.group(1)] += 1
        require(row.get("parent_id") == match.group(1) and row.get("path") == match.group(2),
                f"job parent/path mismatch: {job}")
        for key, prefix in (("manifest", "manifests"), ("spec", "specs")):
            relative = safe_relative(row.get(key), prefix)
            path = root / Path(*relative.parts)
            require(path.is_file() and freight.sha256(path) == row.get(f"{key}_sha256"),
                    f"job {key} binding mismatch: {job}")
    require(len(parents) == 29 and set(parents.values()) == {8},
            "portable queue is not 29 exact eight-leaf parents")

    suffix = ""
    if materialize:
        row = next(item for item in jobs if item["id"] == CANARY)
        with tempfile.TemporaryDirectory(prefix="erdos85-h7-freight-canary.") as raw:
            output = Path(raw) / "canary.cnf"
            command = [sys.executable,
                       str(root / "tools/generate_h7_empty_cube_adaptive_split_jobs.py"),
                       "materialize", "--manifest", str(root / row["manifest"]),
                       "--parent-manifest", str(root / "parent.json"),
                       "--tree-spec", str(root / row["spec"]),
                       "--base", str(root / "base.cnf"), "--leaf", CANARY,
                       "--output", str(output)]
            environment = {**os.environ, "PYTHONDONTWRITEBYTECODE": "1"}
            result = subprocess.run(command, env=environment, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT, text=True)
            require(result.returncode == 0 and output.is_file(),
                    f"canary materialization failed: {result.stdout.strip()}")
            require(output.open().readline().strip() == "p cnf 17633 720828" and
                    freight.sha256(output) == CANARY_SHA,
                    "canary CNF mismatch")
            suffix = f" canary_sha256={CANARY_SHA}"
    return (f"H7 FLEET FREIGHT VERIFIED files={len(actual)} jobs=232 "
            f"freight_sha256={freight.sha256(inventory_path)}" + suffix)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--materialize-canary", action="store_true")
    args = parser.parse_args()
    print(validate(args.root, args.materialize_canary))


if __name__ == "__main__":
    main()
