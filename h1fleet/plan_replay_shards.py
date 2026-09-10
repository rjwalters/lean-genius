#!/usr/bin/env python3
"""Plan disjoint replay queues. No manifest freeze, proof acceptance, or launch.

Weights affect scheduling only. The parent queue must already join the receipted
capacity index. A separate freezer must bind each child to production freight.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from capacity_queue import (CAPACITY_PROFILE_COUNTS, load_capacity_index, validate_queue_capacity,
                            validate_queue_tables, validate_reindex_receipt)
from replay_common import ReplayError, canonical_json, sha256_file
from replay_worker import validate_job

SCHEMA = "erdos85-h1-replay-shard-plan-v1"
WEIGHTS_SCHEMA = "erdos85-h1-replay-shard-weights-v1"
BASE_PREFIX = "sat49/campaign-20260825/h1-replay/fleet/"


def digest(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def read_queue(raw: bytes) -> list[dict]:
    try:
        jobs = [json.loads(line) for line in raw.splitlines()]
    except (ValueError, UnicodeError) as error:
        raise ReplayError("malformed queue JSON") from error
    if not jobs or not all(isinstance(job, dict) for job in jobs):
        raise ReplayError("queue must contain job objects")
    if raw != b"".join(canonical_json(job) for job in jobs):
        raise ReplayError("queue must use canonical JSON lines")
    for job in jobs:
        validate_job(job, job.get("tag"))
    tags = [job["tag"] for job in jobs]
    slots = [(job["profile"], job["local_index"]) for job in jobs]
    keys = [job["certificate_key"] for job in jobs]
    if tags != sorted(set(tags)) or len(slots) != len(set(slots)) or len(keys) != len(set(keys)):
        raise ReplayError("queue tags, slots, and input keys must be unique; tags sorted")
    validate_queue_tables(jobs)
    return jobs


def read_weights(raw: bytes, jobs: list[dict]) -> dict:
    try:
        value = json.loads(raw)
    except (ValueError, UnicodeError) as error:
        raise ReplayError("malformed weights JSON") from error
    if not isinstance(value, dict) or set(value) != {"schema", "unit", "source", "weights"}:
        raise ReplayError("weights fields differ from schema")
    if raw != canonical_json(value) or value["schema"] != WEIGHTS_SCHEMA:
        raise ReplayError("weights must be canonical with the expected schema")
    if value["unit"] not in ("estimated_milliseconds", "raw_bytes", "compressed_gzip_bytes"):
        raise ReplayError("weights require a common declared unit")
    if not isinstance(value["source"], str) or not value["source"].strip():
        raise ReplayError("weight source must be declared")
    weights = value["weights"]
    if not isinstance(weights, dict) or set(weights) != {job["tag"] for job in jobs}:
        raise ReplayError("weights must cover exactly the parent tags")
    if any(type(v) is not int or v <= 0 for v in weights.values()):
        raise ReplayError("weights must be positive integers")
    return value


def validate_prefix(prefix: str) -> None:
    if (not isinstance(prefix, str) or not prefix.startswith(BASE_PREFIX)
            or not prefix.endswith("/") or "\\" in prefix
            or any(part in ("", ".", "..") for part in prefix[:-1].split("/"))
            or len(prefix[len(BASE_PREFIX):-1].split("/")) != 1
            or not prefix[len(BASE_PREFIX):-1]):
        raise ReplayError("prefix must be the normalized fleet/<run-id>/ namespace")


def partition(parent: bytes, weights_raw: bytes, count: int, prefix: str) -> tuple[dict, list[bytes]]:
    jobs = read_queue(parent)
    weight_record = read_weights(weights_raw, jobs)
    validate_prefix(prefix)
    if type(count) is not int or not 1 <= count <= min(999, len(jobs)):
        raise ReplayError("shard count must be positive and produce no empty queue")
    weights = weight_record["weights"]
    buckets: list[list[dict]] = [[] for _ in range(count)]
    loads = [0] * count
    for job in sorted(jobs, key=lambda job: (-weights[job["tag"]], job["tag"])):
        target = min(range(count), key=lambda i: (loads[i], i))
        buckets[target].append(job)
        loads[target] += weights[job["tag"]]
    queues = [b"".join(canonical_json(job) for job in sorted(bucket, key=lambda j: j["tag"]))
              for bucket in buckets]
    plan = {"schema": SCHEMA, "status": "PLAN_ONLY", "launch_ready": False,
            "algorithm": "descending-weight-tag; least-load-shard-id-v1",
            "parent_queue_sha256": digest(parent), "weights_sha256": digest(weights_raw),
            "weight_unit": weight_record["unit"], "prefix": prefix,
            "expected_jobs": len(jobs), "shards": [
                {"id": i, "queue_file": f"shard-{i:03d}.jsonl", "queue_sha256": digest(queue),
                 "campaign_prefix": f"{prefix}shards/{i:03d}/", "jobs": len(buckets[i]),
                 "weight": loads[i]} for i, queue in enumerate(queues)]}
    verify_partition(parent, weights_raw, plan, queues)
    return plan, queues


def verify_partition(parent: bytes, weights_raw: bytes, plan: dict, queues: list[bytes]) -> None:
    """Check conservation and exact job bytes separately from the assignment loop."""
    jobs = read_queue(parent)
    weights = read_weights(weights_raw, jobs)
    expected = {job["tag"]: canonical_json(job) for job in jobs}
    if (not isinstance(plan, dict) or set(plan) != {"schema", "status", "launch_ready", "algorithm", "parent_queue_sha256",
                      "weights_sha256", "weight_unit", "prefix", "expected_jobs", "shards"}
            or plan["schema"] != SCHEMA or plan["status"] != "PLAN_ONLY"
            or plan["launch_ready"] is not False
            or plan["algorithm"] != "descending-weight-tag; least-load-shard-id-v1"
            or plan["parent_queue_sha256"] != digest(parent)
            or plan["weights_sha256"] != digest(weights_raw)
            or plan["weight_unit"] != weights["unit"] or plan["expected_jobs"] != len(jobs)
            or not isinstance(plan["shards"], list) or not plan["shards"]
            or len(plan["shards"]) != len(queues)):
        raise ReplayError("plan identity mismatch")
    validate_prefix(plan["prefix"])
    seen: set[str] = set()
    for i, (row, raw) in enumerate(zip(plan["shards"], queues, strict=True)):
        child = read_queue(raw)
        if (not isinstance(row, dict) or set(row) != {"id", "queue_file", "queue_sha256",
                "campaign_prefix", "jobs", "weight"}
                or type(row["id"]) is not int or type(row["jobs"]) is not int
                or type(row["weight"]) is not int or row["id"] != i or row["queue_file"] != f"shard-{i:03d}.jsonl"
                or row["queue_sha256"] != digest(raw) or row["jobs"] != len(child)
                or row["campaign_prefix"] != f"{plan['prefix']}shards/{i:03d}/"):
            raise ReplayError("shard identity mismatch")
        for job in child:
            tag = job["tag"]
            if tag in seen or expected.get(tag) != canonical_json(job):
                raise ReplayError("shards duplicate, add, or alter a parent job")
            seen.add(tag)
        if row["weight"] != sum(weights["weights"][job["tag"]] for job in child):
            raise ReplayError("shard weight mismatch")
    if seen != set(expected):
        raise ReplayError("shards omit parent jobs")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--queue", type=Path, required=True)
    parser.add_argument("--weights", type=Path, required=True)
    parser.add_argument("--capacity-index", type=Path, required=True)
    parser.add_argument("--reindex-receipt", type=Path, required=True)
    parser.add_argument("--inventory-sha256", required=True)
    parser.add_argument("--shards", type=int, required=True)
    parser.add_argument("--prefix", required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()
    try:
        parent, weights = args.queue.read_bytes(), args.weights.read_bytes()
        jobs = read_queue(parent)
        capacity_sha = sha256_file(args.capacity_index)
        reindex_sha = sha256_file(args.reindex_receipt)
        capacity = load_capacity_index(args.capacity_index)
        reindex = validate_reindex_receipt(args.reindex_receipt, args.capacity_index,
                                           args.inventory_sha256)
        if reindex["emitted_rows"] != len(capacity):
            raise ReplayError("capacity receipt row count mismatch")
        validate_queue_capacity(jobs, capacity, require_complete=False)
        plan, queues = partition(parent, weights, args.shards, args.prefix)
        if (sha256_file(args.capacity_index) != capacity_sha
                or sha256_file(args.reindex_receipt) != reindex_sha):
            raise ReplayError("capacity inputs changed during planning")
        # Exclusive directory creation; incomplete output on failure remains non-ready.
        args.output_dir.mkdir(parents=False, exist_ok=False)
        for row, raw in zip(plan["shards"], queues, strict=True):
            with (args.output_dir / row["queue_file"]).open("xb") as stream:
                stream.write(raw)
        for name, raw in (("parent.jsonl", parent), ("weights.json", weights)):
            with (args.output_dir / name).open("xb") as stream:
                stream.write(raw)
        selected = {job["tag"] for job in jobs}
        excluded = [{"tag": tag, "profile": slot[0], "local_index": slot[1],
                     "status": "UNRESOLVED"} for tag, slot in sorted(capacity.items())
                    if tag not in selected]
        excluded_raw = canonical_json(excluded)
        with (args.output_dir / "excluded-capacity.json").open("xb") as stream:
            stream.write(excluded_raw)
        provenance = {"capacity_rows": len(capacity),
                      "canonical_capacity_rows": sum(CAPACITY_PROFILE_COUNTS),
                      "parent_jobs": len(jobs), "excluded_capacity_rows": len(excluded),
                      "excluded_capacity_sha256": digest(excluded_raw),
                      "accepted_set_sha256": None,
                      "coverage_status": "PARTIAL_INPUT_ONLY; exclusions are not accepted evidence",
                      "schema": "erdos85-h1-replay-shard-inputs-v1",
                      "inventory_sha256": args.inventory_sha256,
                      "capacity_index_sha256": capacity_sha,
                      "reindex_receipt_sha256": reindex_sha,
                      "plan_sha256": digest(canonical_json(plan))}
        with (args.output_dir / "inputs.json").open("xb") as stream:
            stream.write(canonical_json(provenance))
        with (args.output_dir / "plan.json").open("xb") as stream:
            stream.write(canonical_json(plan))
        print(f"PLAN_ONLY jobs={len(jobs)} shards={len(queues)} plan_sha256={provenance['plan_sha256']}")
        return 0
    except (OSError, ReplayError) as error:
        print(f"SHARD_PLAN_ERROR: {error}")
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
