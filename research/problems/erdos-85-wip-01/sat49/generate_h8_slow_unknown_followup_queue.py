#!/usr/bin/env python3
"""Create an authenticated two-child queue for one slow H7 adaptive leaf."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
from pathlib import Path


SCHEMA = "erdos85-h8-slow-unknown-followup-queue-v1"
UNKNOWN_SCHEMA = "erdos85-h7-adaptive-unknown-v1"
MANIFEST_SCHEMA = "erdos85-h7-canonical-empty-cube-adaptive-jobs-v1"
JOB_RE = re.compile(r"cube_F[6-9]_t\d+\.adaptive\.leaf-([01]{3})")


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def parse_marker(path: Path, job: str, cap: int, queue_sha: str,
                 worker_sha: str, cadical_sha: str) -> dict[str, str]:
    fields = path.read_text().split()
    require(len(fields) == 9 and fields[1:3] == [job, "SLOW-UNKNOWN"],
            "malformed SLOW-UNKNOWN marker")
    parsed = dict(field.split("=", 1) for field in fields[3:]
                  if field.count("=") == 1)
    expected = {
        "schema": UNKNOWN_SCHEMA, "rc": "0", "cap_s": str(cap),
        "queue_sha256": queue_sha, "cadical_sha256": cadical_sha,
        "worker_sha256": worker_sha,
    }
    require(parsed == expected, "SLOW-UNKNOWN marker authentication mismatch")
    return parsed


def build_queue(*, job: str, marker: Path, old_manifest: Path,
                new_manifest: Path, new_spec: Path, source_queue: Path,
                source_worker: Path, cadical_sha: str, cap: int) -> dict:
    match = JOB_RE.fullmatch(job)
    require(match is not None, "source job must be an exact depth-3 H7 leaf")
    old_path = match.group(1)
    paths = [marker, old_manifest, new_manifest, new_spec,
             source_queue, source_worker]
    require(all(path.is_file() for path in paths), "a bound input is missing")
    hashes = {path: sha256(path) for path in paths}
    parse_marker(marker, job, cap, hashes[source_queue],
                 hashes[source_worker], cadical_sha)

    old = json.loads(old_manifest.read_text())
    new = json.loads(new_manifest.read_text())
    spec = json.loads(new_spec.read_text())
    require(old.get("schema") == new.get("schema") == MANIFEST_SCHEMA,
            "unsupported adaptive manifest schema")
    require(new.get("tree_spec_sha256") == hashes[new_spec],
            "new manifest is not bound to the supplied spec")
    stable = ("parent_manifest_sha256", "base_sha256", "variables",
              "base_clauses", "parent_id", "parent_units")
    require(all(old.get(key) == new.get(key) for key in stable),
            "new tree changed a stable parent/base field")
    require(new.get("internal_node_count") == old.get("internal_node_count") + 1 and
            new.get("leaf_count") == old.get("leaf_count") + 1,
            "new tree is not a one-node extension")
    old_leaves = {leaf["path"]: leaf for leaf in old.get("leaves", [])}
    new_leaves = {leaf["path"]: leaf for leaf in new.get("leaves", [])}
    require(old_path in old_leaves and old_leaves[old_path].get("id") == job,
            "source leaf is absent from the old manifest")
    require(set(new_leaves) == (set(old_leaves) - {old_path}) |
            {old_path + "0", old_path + "1"},
            "new tree does not replace exactly the source leaf")
    for path in set(old_leaves) - {old_path}:
        require(old_leaves[path] == new_leaves[path],
                f"unrelated leaf changed: {path}")
    parent_units = old_leaves[old_path].get("units")
    require(isinstance(parent_units, list), "malformed source units")
    children = []
    for bit in "01":
        leaf = new_leaves[old_path + bit]
        units = leaf.get("units")
        require(isinstance(units, list) and len(units) == len(parent_units) + 1 and
                units[:-1] == parent_units and type(units[-1]) is int and units[-1] != 0,
                f"malformed child units: {old_path + bit}")
        children.append({
            "id": leaf["id"], "path": leaf["path"], "units": units,
            "manifest": str(new_manifest.resolve()),
            "manifest_sha256": hashes[new_manifest],
            "spec": str(new_spec.resolve()), "spec_sha256": hashes[new_spec],
        })
    require(children[0]["units"][-1] == -children[1]["units"][-1] < 0,
            "children are not the negative/positive branches of one variable")
    return {
        "schema": SCHEMA, "source_job": job, "cap_s": cap,
        "source_unknown_marker": str(marker.resolve()),
        "source_unknown_marker_sha256": hashes[marker],
        "source_queue": str(source_queue.resolve()),
        "source_queue_sha256": hashes[source_queue],
        "source_worker": str(source_worker.resolve()),
        "source_worker_sha256": hashes[source_worker],
        "cadical_sha256": cadical_sha,
        "parent_manifest_sha256": new["parent_manifest_sha256"],
        "base_sha256": new["base_sha256"],
        "split_variable": abs(children[0]["units"][-1]),
        "job_count": 2, "jobs": children,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--job", required=True)
    parser.add_argument("--marker", type=Path, required=True)
    parser.add_argument("--old-manifest", type=Path, required=True)
    parser.add_argument("--new-manifest", type=Path, required=True)
    parser.add_argument("--new-spec", type=Path, required=True)
    parser.add_argument("--source-queue", type=Path, required=True)
    parser.add_argument("--source-worker", type=Path, required=True)
    parser.add_argument("--cadical-sha256", required=True)
    parser.add_argument("--cap", type=int, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    require(re.fullmatch(r"[0-9a-f]{64}", args.cadical_sha256) is not None,
            "invalid CaDiCaL digest")
    require(1 <= args.cap <= 86400, "invalid solve cap")
    queue = build_queue(
        job=args.job, marker=args.marker.resolve(),
        old_manifest=args.old_manifest.resolve(),
        new_manifest=args.new_manifest.resolve(), new_spec=args.new_spec.resolve(),
        source_queue=args.source_queue.resolve(),
        source_worker=args.source_worker.resolve(),
        cadical_sha=args.cadical_sha256, cap=args.cap)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    temporary = args.output.with_name(f".{args.output.name}.{os.getpid()}.tmp")
    temporary.write_text(json.dumps(queue, indent=2, sort_keys=True) + "\n")
    os.replace(temporary, args.output)
    print(f"WROTE {args.output.resolve()} sha256={sha256(args.output)}")


if __name__ == "__main__":
    main()
