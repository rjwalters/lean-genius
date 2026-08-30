#!/usr/bin/env python3
"""Build a relocatable, hash-pinned freight tree for the H7 leaf fleet."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import tempfile
from pathlib import Path


QUEUE_SHA = "3af3c6b13648328f29f488e1143e194cdf8c608df461cab81c45f7d72cbcdedb"
PARENT_SHA = "e298e181f67e2f50d88fa61f71516cb86af31948e26413894bb3b147f51020c6"
BASE_SHA = "8bc9b8f15b7f03194f39d208b2c0015e6039e0aac759ccfce0b6415724130eb0"
SCHEMA = "erdos85-h7-fleet-portable-freight-v1"
TOOLS = (
    "generate_h7_empty_cube_adaptive_split_jobs.py",
    "generate_h7_adaptive_binary_tree_jobs.py",
    "generate_h7_empty_cube_manifest.py",
    "probe_h7_binary_lookahead.py",
    "compact_h1_v2_lrat.py",
    "verify_dimacs_model.py",
)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def relative_rows(queue: dict, source_root: Path) -> tuple[list[dict], set[Path], set[Path]]:
    jobs = queue.get("jobs")
    require(isinstance(jobs, list) and len(jobs) == 232, "expected 232 source jobs")
    manifests, specs, result = set(), set(), []
    for row in jobs:
        manifest, spec = Path(row.get("manifest", "")), Path(row.get("spec", ""))
        require(manifest.parent == source_root / "manifests", "manifest escapes source root")
        require(spec.parent == source_root / "specs", "spec escapes source root")
        require(manifest.is_file() and sha256(manifest) == row.get("manifest_sha256"),
                "manifest hash mismatch")
        require(spec.is_file() and sha256(spec) == row.get("spec_sha256"),
                "spec hash mismatch")
        manifests.add(manifest); specs.add(spec)
        result.append({**row, "manifest": f"manifests/{manifest.name}",
                       "spec": f"specs/{spec.name}"})
    require(len(manifests) == len(specs) == 29, "expected 29 manifest/spec pairs")
    return result, manifests, specs


def build(source_root: Path, base: Path, tools_root: Path, output: Path) -> None:
    queue_path, parent = source_root / "queue.json", source_root / "parent.json"
    require(sha256(queue_path) == QUEUE_SHA, "source queue hash mismatch")
    require(sha256(parent) == PARENT_SHA, "source parent hash mismatch")
    require(sha256(base) == BASE_SHA, "source base hash mismatch")
    require(not output.exists(), "output already exists")
    queue = json.loads(queue_path.read_text())
    rows, manifests, specs = relative_rows(queue, source_root)
    tool_paths = [tools_root / name for name in TOOLS]
    require(all(path.is_file() for path in tool_paths), "a required tool is missing")

    output.parent.mkdir(parents=True, exist_ok=True)
    temporary = Path(tempfile.mkdtemp(prefix=f".{output.name}.", dir=output.parent))
    try:
        for name in ("manifests", "specs", "tools"):
            (temporary / name).mkdir()
        shutil.copy2(parent, temporary / "parent.json")
        shutil.copy2(base, temporary / "base.cnf")
        for path in sorted(manifests): shutil.copy2(path, temporary / "manifests" / path.name)
        for path in sorted(specs): shutil.copy2(path, temporary / "specs" / path.name)
        for path in tool_paths: shutil.copy2(path, temporary / "tools" / path.name)
        portable_queue = {
            "schema": "erdos85-h7-canonical-empty-cube-adaptive-portable-queue-v1",
            "source_schema": queue.get("schema"), "source_queue_sha256": QUEUE_SHA,
            "parent_manifest": "parent.json", "parent_manifest_sha256": PARENT_SHA,
            "base": "base.cnf", "base_sha256": BASE_SHA,
            "parent_count": queue.get("parent_count"), "leaf_count": 232, "jobs": rows,
        }
        (temporary / "queue.json").write_text(
            json.dumps(portable_queue, indent=2, sort_keys=True) + "\n")
        files = sorted(path for path in temporary.rglob("*") if path.is_file())
        inventory = {
            "schema": SCHEMA, "source_queue_sha256": QUEUE_SHA,
            "file_count": len(files),
            "files": {str(path.relative_to(temporary)): sha256(path) for path in files},
        }
        (temporary / "freight.json").write_text(
            json.dumps(inventory, indent=2, sort_keys=True) + "\n")
        os.replace(temporary, output)
    except BaseException:
        shutil.rmtree(temporary, ignore_errors=True)
        raise


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-root", type=Path, required=True)
    parser.add_argument("--base", type=Path, required=True)
    parser.add_argument("--tools-root", type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    build(args.source_root.resolve(), args.base.resolve(), args.tools_root.resolve(),
          args.output.resolve())
    print(f"WROTE {args.output.resolve()} freight_sha256={sha256(args.output / 'freight.json')}")


if __name__ == "__main__":
    main()
