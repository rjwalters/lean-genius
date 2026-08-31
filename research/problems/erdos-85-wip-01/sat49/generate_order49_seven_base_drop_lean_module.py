#!/usr/bin/env python3
"""Generate the provenance-bound seven-base order-49 drop wrapper."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import stat
import subprocess
from pathlib import Path, PurePosixPath


LEAN_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)+")
SHA256 = re.compile(r"[0-9a-f]{64}")
SCHEMA = "erdos85-order49-seven-base-drop-inputs-v1"
SMALL_HIGH = (
    ("hb1", "h3_b1", "Erdos85.smallHighH3B1Base_unsat"),
    ("hc1", "h3_c1", "Erdos85.smallHighH3C1Base_unsat"),
    ("hc2", "h3_c2", "Erdos85.smallHighH3C2Base_unsat"),
    ("hdist2", "h3_dist2", "Erdos85.smallHighH3Dist2Base_unsat"),
    ("h50", "h5_t0", "Erdos85.smallHighH5T0Base_unsat"),
    ("h51", "h5_t1", "Erdos85.smallHighH5T1Base_unsat"),
    ("h52", "h5_t2", "Erdos85.smallHighH5T2Base_unsat"),
)
EXPECTED_INPUTS = (
    ("h1", "Proofs.Generated.Erdos85OrderFortyNineOneHighCertificates",
     "Erdos85.orderFortyNineStratumExcluded_one_of_generatedCertificates"),
    *((argument, "Proofs.Generated.Erdos85OrderFortyNineSmallHighCertificates", theorem)
      for argument, _, theorem in SMALL_HIGH),
    ("h7", "Proofs.Generated.Erdos85OrderFortyNineSevenHighCertificates",
     "Erdos85.orderFortyNineStratumExcluded_seven_of_generatedCertificates"),
)
CORE_FIELDS = {
    "consumer_argument", "theorem", "source_module", "source_sha256",
    "source_path", "aggregate_receipt_sha256", "aggregate_receipt_path",
}
RECEIPT_SCHEMA = "erdos85-order49-wrapper-provenance-v1"
FINAL_RECEIPT_SCHEMA = "erdos85-h1-wrapper-endpoint-receipt-v1"
FINALIZER_PRODUCER_PATH = "research/problems/erdos-85-wip-01/sat49/finalize_h1_wrapper_endpoint_receipt.py"
# Banked finalizer identity. Keeping the optional type lets the test suite prove
# that production use fails closed if a future transition clears the pin.
FINALIZER_PRODUCER_SHA256: str | None = "21514e3f43fcd797d8a724633a329c5fe1b91068ab5aa83d1600509269167ff4"
CELL_RECEIPT_SCHEMA = "erdos85-small-high-cell-aggregate-v1"
CELL_INDEX_SCHEMA = "erdos85-small-high-cell-aggregate-index-v1"
FORBIDDEN_MODULE_PARTS = ("SmallHighDropFrontier", "PartitionedCanonicalDropFrontier")
FINAL_FIELDS = {"artifacts", "audit_identity", "cache_identity_sha256", "compiled_cone_identity_sha256",
    "compiled_cone_size", "consumer_projection_identity", "control_identities", "endpoint_identity", "image",
    "producer_identity", "producer_path", "producer_sha256", "repo", "review_id", "schema", "source_commit",
    "terminal_capacity", "tool_identities", "upstream_receipts"}
ENDPOINT_FIELDS = {"generated_tree_identity_sha256", "module", "olean_bytes", "olean_path", "olean_sha256",
    "original_source_path", "source_blob_oid", "source_bytes", "source_path", "source_sha256", "theorem"}
TERMINAL_FIELDS = {"adapter_receipt_sha256", "aggregate_layout_sha256", "bank_receipt_sha256",
    "capacity_reindex_receipt_sha256", "coverage_receipt_sha256", "evidence_sha256", "leaf_count",
    "leaf_module_index_sha256", "payload_identity_sha256", "payload_index_sha256", "profile_counts",
    "replay_audit_sha256", "replay_evidence_identity_sha256", "status", "terminal_counts"}
PROFILE_COUNTS = [1485, 3617, 4717, 2693, 839]
TERMINAL_COUNTS = {"certified": 13351, "fleet_in_flight": 0, "pending": 0, "status_total": 13351}
OID = re.compile(r"[0-9a-f]{40}")
H1_IMAGE = "lean4-arm64@sha256:a5ca6c4e3328a1832d5f9b814ab7c1e35616903b3956341962a5b1a96fb6dff6"
AXIOM_PRODUCER_SHA256 = "3014e81a3a056c88e44811f4f76032b3537e0c36622c1607d29c72979872035e"
UPSTREAM_SCHEMAS = {"axiom": "erdos85-h1-endpoint-axiom-audit-v1",
    "cache_manifest": "erdos85-h1-offline-dependency-cache-v1",
    "cache_snapshot": "erdos85-h1-offline-dependency-cache-snapshot-receipt-v1",
    "cold": "erdos85-h1-endpoint-cold-build-v1", "post_module": "erdos85-h1-leaf-module-evidence-receipt-v1"}
RETAINED_FIELDS = {
    "axiom": {"allowlist_path", "allowlist_sha256", "artifacts", "audited_source_identities",
        "cache_manifest_path", "cache_manifest_sha256", "cache_snapshot_receipt_path",
        "cache_snapshot_receipt_sha256", "cold_receipt_path", "cold_receipt_sha256", "commands",
        "endpoint_module", "endpoint_theorem", "foundational_axioms", "image", "native_root_count",
        "producer_path", "producer_sha256", "project_cone_source_identities", "schema", "source_commit",
        "theorem_count", "tool_identities", "toolchain_path", "toolchain_sha256"},
    "cold": {"cache_identity_sha256", "cache_manifest_path", "cache_manifest_sha256",
        "cache_snapshot_producer_identity", "cache_snapshot_producer_sha256", "cache_snapshot_receipt_path",
        "cache_snapshot_receipt_sha256", "commands", "endpoint_module", "endpoint_source_path",
        "endpoint_source_sha256", "endpoint_theorem", "generated_tree_identity_sha256", "image",
        "post_module_receipt_path", "post_module_receipt_sha256", "producer_path", "producer_sha256",
        "resource_policy", "retained_generated_artifacts", "review_id", "reviewed_control_files", "schema",
        "source_commit", "target_generated_artifact_path", "target_olean_build_path", "target_olean_bytes",
        "target_olean_path", "target_olean_sha256", "toolchain_path", "toolchain_sha256"},
    "cache_manifest": {"entries", "identity_sha256", "root", "schema"},
    "cache_snapshot": {"cache_manifest_path", "cache_manifest_sha256", "control_files", "entry_count",
        "git_path", "git_sha256", "package_count", "packages", "producer_path", "producer_sha256", "repo",
        "schema", "source_commit"},
    "post_module": {"adapter_receipt_path", "adapter_receipt_sha256", "aggregate_layout_path",
        "aggregate_layout_sha256", "bank_receipt_path", "bank_receipt_sha256", "capacity_reindex_receipt_path",
        "capacity_reindex_receipt_sha256", "commit_object_oid", "endpoint_module", "endpoint_source_path",
        "endpoint_source_sha256", "endpoint_theorem", "evidence_path", "evidence_sha256",
        "generated_tree_identity_sha256", "leaf_count", "leaf_module_index_path", "leaf_module_index_sha256",
        "producer_path", "producer_sha256", "profile_counts", "repo", "review_id", "reviewed_commit", "schema"},
    "bank": {"all_even_manifest_path", "all_even_manifest_sha256", "capacity_inventory_path",
        "capacity_inventory_sha256", "compact_universe_path", "compact_universe_sha256",
        "complement_manifest_path", "complement_manifest_sha256", "coverage_receipt_path",
        "coverage_receipt_sha256", "coverage_terminal_counts", "leaf_count", "ledger_snapshot_path",
        "ledger_snapshot_sha256", "materializer_sha256", "materializer_source", "payload_identity_sha256",
        "payload_index_path", "payload_index_sha256", "profile_counts", "replay_audit_path",
        "replay_audit_sha256", "s3_bucket", "s3_prefix", "schema", "selected_ledger_identity_sha256",
        "source_index_path", "source_index_sha256", "toolchain_path", "toolchain_sha256"},
    "evidence": {"adapter_repo_path", "adapter_source_identity", "aggregate_layout_source_identity",
        "aggregate_tree_identity_sha256", "generated_tree_identity_sha256", "leaf_count",
        "leaf_tree_identity_sha256", "profile_counts", "review_id", "reviewed_commit", "rows", "schema"},
    "payload": {"capacity_inventory_sha256", "profile_counts", "rows", "schema"},
    "replay": {"capacity_inventory_sha256", "coverage_receipt_sha256", "profile_counts", "rows",
        "replay_evidence_identity_sha256", "schema"},
    "coverage": {"aws", "host_ledger_snapshot", "inputs", "live_campaign", "live_named_output_paths",
        "live_named_outputs_mutated", "live_outputs_after", "live_outputs_before", "outputs", "schema",
        "summary", "timestamp_utc"},
}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def canonical_receipt(identity: dict) -> bytes:
    return (json.dumps(identity, ensure_ascii=True, allow_nan=False,
                       sort_keys=True, separators=(",", ":")) + "\n").encode()

def _regular(path: Path, label: str) -> Path:
    if not path.is_absolute() or path != path.resolve(strict=True):
        raise ValueError(f"{label}: path is not canonical absolute")
    cursor = path
    while True:
        if stat.S_ISLNK(os.lstat(cursor).st_mode): raise ValueError(f"{label}: symlink ancestry")
        if cursor.parent == cursor: break
        cursor = cursor.parent
    if not stat.S_ISREG(os.stat(path, follow_symlinks=False).st_mode): raise ValueError(f"{label}: not regular")
    return path

def _snapshot(path: Path, label: str) -> tuple[str, int, int, int]:
    _regular(path, label); info = os.stat(path, follow_symlinks=False)
    if info.st_nlink != 1: raise ValueError(f"{label}: hardlink alias")
    return sha256(path), info.st_size, info.st_dev, info.st_ino

def _recheck(path: Path, pin: tuple[str, int, int, int], label: str) -> None:
    if _snapshot(path, label) != pin: raise ValueError(f"{label}: input drift")

def _relative(text: object, label: str) -> PurePosixPath:
    if not isinstance(text, str) or not text or "\\" in text: raise ValueError(f"{label}: bad relative path")
    path = PurePosixPath(text)
    if path.is_absolute() or path.as_posix() != text or any(x in ("", ".", "..") for x in path.parts):
        raise ValueError(f"{label}: bad relative path")
    return path

def _git(repo: Path, args: list[str], runner=None) -> list[str]:
    if runner is None:
        result = subprocess.run(["git", "-C", str(repo), *args], check=True, stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE, text=True)
        return result.stdout.splitlines()
    value = runner(args, repo)
    if not isinstance(value, list) or not all(isinstance(x, str) for x in value):
        raise ValueError("Git runner result malformed")
    return value

def _validate_h1_final(row: dict, pins: dict[Path, tuple[str, int, int, int]], runner=None) -> None:
    final_path = _regular(Path(row["final_receipt_path"]), "h1 final receipt")
    if sha256(final_path) != row["final_receipt_sha256"] or final_path.name != "receipt.json":
        raise ValueError("h1 final receipt identity mismatch")
    raw = final_path.read_bytes(); final = json.loads(raw)
    if (not isinstance(final, dict) or set(final) != FINAL_FIELDS or raw != canonical_receipt(final)
            or final.get("schema") != FINAL_RECEIPT_SCHEMA):
        raise ValueError("h1 final receipt schema/serialization mismatch")
    deferred = FINALIZER_PRODUCER_SHA256
    if deferred is None or not SHA256.fullmatch(deferred): raise ValueError("finalizer producer SHA is not banked")
    repo = Path(final.get("repo", "")); _regular(repo / FINALIZER_PRODUCER_PATH, "finalizer producer")
    producer = final.get("producer_identity")
    if (final.get("producer_path") != str(repo / FINALIZER_PRODUCER_PATH) or final.get("producer_sha256") != deferred
            or not isinstance(producer, dict) or set(producer) != {"blob_oid", "bytes", "commit", "path", "sha256"}
            or producer != {"blob_oid": producer.get("blob_oid"), "bytes": (repo / FINALIZER_PRODUCER_PATH).stat().st_size,
                            "commit": final.get("source_commit"), "path": FINALIZER_PRODUCER_PATH, "sha256": deferred}
            or not OID.fullmatch(str(producer.get("blob_oid"))) or not OID.fullmatch(str(final.get("source_commit")))
            or sha256(repo / FINALIZER_PRODUCER_PATH) != deferred):
        raise ValueError("finalizer producer identity mismatch")
    pins[repo / FINALIZER_PRODUCER_PATH] = _snapshot(repo / FINALIZER_PRODUCER_PATH, "finalizer producer")
    root = final_path.parent; artifacts = final.get("artifacts")
    if not isinstance(artifacts, list): raise ValueError("final artifact inventory missing")
    by_path = {}; actual = set(); actual_dirs = set(); artifact_inodes = set()
    for path in root.rglob("*"):
        if path.is_symlink() or (not path.is_dir() and not path.is_file()): raise ValueError("final tree special entry")
        if path.is_dir(): actual_dirs.add(path.relative_to(root).as_posix())
        elif path != final_path: actual.add(path.relative_to(root).as_posix())
    for item in artifacts:
        if (not isinstance(item, dict) or set(item) != {"bytes", "path", "sha256"} or type(item["bytes"]) is not int
                or item["bytes"] < 0 or not SHA256.fullmatch(str(item["sha256"])) or item["path"] in by_path):
            raise ValueError("final artifact row malformed")
        relative = _relative(item["path"], "final artifact"); path = root / Path(*relative.parts)
        pin = _snapshot(path, "final artifact")
        if (pin[0], pin[1]) != (item["sha256"], item["bytes"]): raise ValueError("final artifact identity mismatch")
        if os.stat(path, follow_symlinks=False).st_nlink != 1: raise ValueError("final artifact has hardlink alias")
        if pin[2:] in artifact_inodes: raise ValueError("final artifacts alias")
        artifact_inodes.add(pin[2:])
        pins[path] = pin; by_path[item["path"]] = item
    expected_dirs = {parent.as_posix() for name in by_path for parent in PurePosixPath(name).parents
                     if parent.as_posix() not in ("", ".")}
    if set(by_path) != actual or actual_dirs != expected_dirs: raise ValueError("final artifact tree is not exact")
    endpoint = final.get("endpoint_identity")
    if not isinstance(endpoint, dict) or set(endpoint) != ENDPOINT_FIELDS: raise ValueError("endpoint identity malformed")
    expected_module, expected_theorem = EXPECTED_INPUTS[0][1], EXPECTED_INPUTS[0][2]
    source_relative = _relative(endpoint["source_path"], "endpoint source"); olean_relative = _relative(endpoint["olean_path"], "endpoint olean")
    source = root / Path(*source_relative.parts); olean = root / Path(*olean_relative.parts)
    if ((endpoint["module"], endpoint["theorem"]) != (expected_module, expected_theorem)
            or source != Path(row["source_path"]) or endpoint["source_sha256"] != row["source_sha256"]
            or by_path.get(endpoint["source_path"], {}).get("sha256") != endpoint["source_sha256"]
            or by_path.get(endpoint["olean_path"], {}).get("sha256") != endpoint["olean_sha256"]
            or by_path.get(endpoint["source_path"], {}).get("bytes") != endpoint["source_bytes"]
            or by_path.get(endpoint["olean_path"], {}).get("bytes") != endpoint["olean_bytes"]
            or not OID.fullmatch(str(endpoint["source_blob_oid"]))
            or not SHA256.fullmatch(str(endpoint["generated_tree_identity_sha256"]))
            or re.search(rf"\b{re.escape(expected_theorem.split('.')[-1])}\b", source.read_text()) is None):
        raise ValueError("endpoint retained identity mismatch")
    original = _relative(endpoint["original_source_path"], "endpoint original source")
    original_path = repo / Path(*original.parts); original_pin = _snapshot(original_path, "endpoint original source")
    pins[original_path] = original_pin
    if original_pin[:2] != (endpoint["source_sha256"], endpoint["source_bytes"]): raise ValueError("endpoint original/retained mismatch")
    projection = final.get("consumer_projection_identity")
    if (not isinstance(projection, dict) or set(projection) != {"bytes", "path", "schema", "sha256"}
            or projection["schema"] != RECEIPT_SCHEMA or root / Path(*_relative(projection["path"], "projection").parts) != Path(row["aggregate_receipt_path"])
            or projection["sha256"] != row["aggregate_receipt_sha256"]
            or by_path.get(projection["path"], {}).get("bytes") != projection["bytes"]
            or by_path.get(projection["path"], {}).get("sha256") != projection["sha256"]):
        raise ValueError("consumer projection identity mismatch")
    terminal = final.get("terminal_capacity")
    if (not isinstance(terminal, dict) or set(terminal) != TERMINAL_FIELDS or terminal.get("status") != "PASS"
            or terminal.get("leaf_count") != 13351 or terminal.get("profile_counts") != PROFILE_COUNTS
            or terminal.get("terminal_counts") != TERMINAL_COUNTS
            or any(not SHA256.fullmatch(str(terminal[key])) for key in TERMINAL_FIELDS - {"status", "leaf_count", "profile_counts", "terminal_counts"})):
        raise ValueError("terminal capacity identity mismatch")
    if (final.get("image") != H1_IMAGE or re.fullmatch(r"[0-9]+", str(final.get("review_id", ""))) is None
            or not SHA256.fullmatch(str(final.get("cache_identity_sha256")))
            or not SHA256.fullmatch(str(final.get("compiled_cone_identity_sha256")))
            or type(final.get("compiled_cone_size")) is not int or final["compiled_cone_size"] <= 0):
        raise ValueError("final build identity mismatch")
    audit = final.get("audit_identity")
    if (not isinstance(audit, dict) or set(audit) != {"foundational_axioms", "native_root_count", "producer_sha256",
            "project_cone_identity_sha256", "status", "theorem_count"} or audit.get("status") != "PASS"
            or audit.get("foundational_axioms") != ["Classical.choice", "Quot.sound", "propext"]
            or audit.get("producer_sha256") != AXIOM_PRODUCER_SHA256
            or type(audit.get("native_root_count")) is not int or audit["native_root_count"] <= 0
            or type(audit.get("theorem_count")) is not int or audit["theorem_count"] <= 0
            or not SHA256.fullmatch(str(audit.get("project_cone_identity_sha256")))):
        raise ValueError("final audit identity mismatch")
    controls = final.get("control_identities")
    expected_controls = ["proofs/lean-toolchain", "proofs/lakefile.toml", "proofs/lake-manifest.json"]
    if (not isinstance(controls, list) or [item.get("path") if isinstance(item, dict) else None for item in controls] != expected_controls
            or any(set(item) != {"blob_oid", "bytes", "path", "sha256"} or not OID.fullmatch(str(item["blob_oid"]))
                   or type(item["bytes"]) is not int or item["bytes"] <= 0 or not SHA256.fullmatch(str(item["sha256"])) for item in controls)):
        raise ValueError("final control identity mismatch")
    for item in controls:
        control_path = repo / Path(*_relative(item["path"], "control source").parts)
        pin = _snapshot(control_path, "control source"); pins[control_path] = pin
        if pin[:2] != (item["sha256"], item["bytes"]): raise ValueError("final control source mismatch")
    tools = final.get("tool_identities")
    if (not isinstance(tools, dict) or set(tools) != {"python_sha256", "lean_sha256", "lake_sha256"}
            or any(not SHA256.fullmatch(str(value)) for value in tools.values())):
        raise ValueError("final tool identity mismatch")
    upstream = final.get("upstream_receipts")
    if not isinstance(upstream, dict) or set(upstream) != {"axiom", "cache_manifest", "cache_snapshot", "cold", "post_module"}:
        raise ValueError("final upstream receipt inventory mismatch")
    for name, identity in upstream.items():
        if (not isinstance(identity, dict) or set(identity) != {"bytes", "path", "schema", "sha256"}
                or identity["schema"] != UPSTREAM_SCHEMAS[name]
                or by_path.get(identity["path"], {}).get("sha256") != identity["sha256"]
                or by_path.get(identity["path"], {}).get("bytes") != identity["bytes"]):
            raise ValueError(f"final upstream receipt mismatch: {name}")

    def retained_json(relative: str, schema: str, contract: str, label: str) -> dict:
        item = by_path.get(relative)
        if item is None: raise ValueError(f"{label} is not retained")
        path = root / Path(*_relative(relative, label).parts); raw = path.read_bytes(); value = json.loads(raw)
        if (not isinstance(value, dict) or set(value) != RETAINED_FIELDS[contract]
                or raw != canonical_receipt(value) or value.get("schema") != schema
                or sha256(path) != item["sha256"] or len(raw) != item["bytes"]):
            raise ValueError(f"{label} schema/serialization mismatch")
        return value

    axiom = retained_json(upstream["axiom"]["path"], UPSTREAM_SCHEMAS["axiom"], "axiom", "retained axiom receipt")
    cold = retained_json(upstream["cold"]["path"], UPSTREAM_SCHEMAS["cold"], "cold", "retained cold receipt")
    cache = retained_json(upstream["cache_manifest"]["path"], UPSTREAM_SCHEMAS["cache_manifest"], "cache_manifest", "retained cache manifest")
    cache_snapshot = retained_json(upstream["cache_snapshot"]["path"], UPSTREAM_SCHEMAS["cache_snapshot"], "cache_snapshot", "retained cache snapshot")
    post = retained_json(upstream["post_module"]["path"], UPSTREAM_SCHEMAS["post_module"], "post_module", "retained post receipt")
    bank = retained_json("evidence/post-chain/bank-receipt.json", "erdos85-h1-capacity-payload-bank-v1", "bank", "retained bank receipt")
    evidence = retained_json("evidence/post/leaf-evidence.json", "erdos85-h1-committed-leaf-evidence-v1", "evidence", "retained leaf evidence")
    payload = retained_json("evidence/post-chain/payload-index.json", "erdos85-h1-capacity-payload-index-v1", "payload", "retained payload index")
    replay = retained_json("evidence/post-chain/replay-audit.json", "erdos85-h1-capacity-replay-audit-v1", "replay", "retained replay audit")
    coverage = retained_json("evidence/post-chain/coverage/receipt.json", "erdos85-h1-coverage-audit-snapshot-v1", "coverage", "retained coverage receipt")
    compiled = cold.get("retained_generated_artifacts")
    project_sources = axiom.get("project_cone_source_identities")
    cache_entries = cache.get("entries")
    payload_rows = payload.get("rows")
    replay_rows = replay.get("rows")
    coverage_summary = coverage.get("summary")
    if (not isinstance(compiled, list) or not compiled
            or final["compiled_cone_size"] != len(compiled)
            or final["compiled_cone_identity_sha256"] != hashlib.sha256(canonical_receipt(compiled)).hexdigest()
            or not isinstance(cache_entries, list)
            or cache.get("identity_sha256") != hashlib.sha256(canonical_receipt(cache_entries)).hexdigest()
            or final["cache_identity_sha256"] != cache["identity_sha256"]
            or cache_snapshot.get("cache_manifest_sha256") != upstream["cache_manifest"]["sha256"]
            or cold.get("cache_manifest_sha256") != upstream["cache_manifest"]["sha256"]
            or cold.get("cache_identity_sha256") != cache["identity_sha256"]
            or cold.get("post_module_receipt_sha256") != upstream["post_module"]["sha256"]
            or axiom.get("cold_receipt_sha256") != upstream["cold"]["sha256"]
            or axiom.get("cache_manifest_sha256") != upstream["cache_manifest"]["sha256"]
            or axiom.get("cache_snapshot_receipt_sha256") != upstream["cache_snapshot"]["sha256"]):
        raise ValueError("retained cold/cache/upstream identity mismatch")
    if (not isinstance(project_sources, list)
            or audit["project_cone_identity_sha256"] != hashlib.sha256(canonical_receipt(project_sources)).hexdigest()
            or audit["foundational_axioms"] != axiom.get("foundational_axioms")
            or audit["native_root_count"] != axiom.get("native_root_count")
            or audit["theorem_count"] != axiom.get("theorem_count")
            or audit["producer_sha256"] != axiom.get("producer_sha256")):
        raise ValueError("retained axiom audit identity mismatch")
    if (tools != axiom.get("tool_identities")
            or controls != cache_snapshot.get("control_files")
            or controls != cold.get("reviewed_control_files")
            or final["image"] != axiom.get("image") or final["image"] != cold.get("image")
            or final["source_commit"] != axiom.get("source_commit")
            or final["source_commit"] != cold.get("source_commit")
            or final["source_commit"] != cache_snapshot.get("source_commit")
            or final["source_commit"] != post.get("reviewed_commit")
            or final["source_commit"] != post.get("commit_object_oid")
            or final["source_commit"] != evidence.get("reviewed_commit")
            or final["review_id"] != cold.get("review_id")
            or final["review_id"] != post.get("review_id")
            or final["review_id"] != evidence.get("review_id")):
        raise ValueError("retained control/tool/build identity mismatch")
    if (post.get("bank_receipt_sha256") != by_path["evidence/post-chain/bank-receipt.json"]["sha256"]
            or post.get("evidence_sha256") != by_path["evidence/post/leaf-evidence.json"]["sha256"]
            or post.get("leaf_count") != terminal["leaf_count"] or post.get("profile_counts") != terminal["profile_counts"]
            or post.get("generated_tree_identity_sha256") != endpoint["generated_tree_identity_sha256"]
            or terminal["adapter_receipt_sha256"] != post.get("adapter_receipt_sha256")
            or terminal["aggregate_layout_sha256"] != post.get("aggregate_layout_sha256")
            or terminal["bank_receipt_sha256"] != post.get("bank_receipt_sha256")
            or terminal["capacity_reindex_receipt_sha256"] != post.get("capacity_reindex_receipt_sha256")
            or terminal["evidence_sha256"] != post.get("evidence_sha256")
            or terminal["leaf_module_index_sha256"] != post.get("leaf_module_index_sha256")):
        raise ValueError("retained post/terminal identity mismatch")
    if (bank.get("leaf_count") != terminal["leaf_count"] or bank.get("profile_counts") != terminal["profile_counts"]
            or bank.get("coverage_terminal_counts") != terminal["terminal_counts"]
            or terminal["payload_identity_sha256"] != bank.get("payload_identity_sha256")
            or terminal["payload_index_sha256"] != bank.get("payload_index_sha256")
            or terminal["replay_audit_sha256"] != bank.get("replay_audit_sha256")
            or terminal["coverage_receipt_sha256"] != bank.get("coverage_receipt_sha256")
            or bank.get("payload_index_sha256") != by_path["evidence/post-chain/payload-index.json"]["sha256"]
            or bank.get("replay_audit_sha256") != by_path["evidence/post-chain/replay-audit.json"]["sha256"]
            or bank.get("coverage_receipt_sha256") != by_path["evidence/post-chain/coverage/receipt.json"]["sha256"]):
        raise ValueError("retained bank/terminal identity mismatch")
    if (not isinstance(payload_rows, list) or len(payload_rows) != terminal["leaf_count"]
            or bank["payload_identity_sha256"] != hashlib.sha256(canonical_receipt([{"bytes": item["packed_lz4_bytes"],
                "path": item["packed_lz4_path"], "sha256": item["packed_lz4_sha256"]} for item in payload_rows])).hexdigest()
            or payload.get("profile_counts") != terminal["profile_counts"]
            or not isinstance(replay_rows, list) or len(replay_rows) != terminal["leaf_count"]
            or replay.get("profile_counts") != terminal["profile_counts"]
            or replay.get("replay_evidence_identity_sha256") != hashlib.sha256(canonical_receipt(replay_rows)).hexdigest()
            or terminal["replay_evidence_identity_sha256"] != replay.get("replay_evidence_identity_sha256")
            or evidence.get("leaf_count") != terminal["leaf_count"] or evidence.get("profile_counts") != terminal["profile_counts"]
            or evidence.get("generated_tree_identity_sha256") != endpoint["generated_tree_identity_sha256"]
            or not isinstance(coverage_summary, dict)
            or {key: coverage_summary.get(key) for key in TERMINAL_COUNTS} != TERMINAL_COUNTS):
        raise ValueError("retained payload/replay/coverage identity mismatch")
    commit_paths = [FINALIZER_PRODUCER_PATH, endpoint["original_source_path"], *expected_controls]
    commit = final["source_commit"]
    commit_oids = _git(repo, ["rev-parse", *[f"{commit}:{path}" for path in commit_paths]], runner)
    work_oids = _git(repo, ["hash-object", "--", *commit_paths], runner)
    expected_git_oids = [producer["blob_oid"], endpoint["source_blob_oid"], *[item["blob_oid"] for item in controls]]
    if commit_oids != work_oids or commit_oids != expected_git_oids:
        raise ValueError("final Git source identity mismatch")


def _validate_core(row: dict, argument: str, singleton: bool) -> dict:
    if not isinstance(row, dict) or not CORE_FIELDS <= set(row):
        raise ValueError(f"{argument}: missing provenance fields")
    if row["consumer_argument"] != argument:
        raise ValueError(f"expected consumer_argument {argument}")
    for field in ("theorem", "source_module"):
        if not isinstance(row[field], str) or not LEAN_NAME.fullmatch(row[field]):
            raise ValueError(f"{argument}: invalid fully-qualified {field}")
    for field in ("source_sha256", "aggregate_receipt_sha256"):
        if not isinstance(row[field], str) or not SHA256.fullmatch(row[field]):
            raise ValueError(f"{argument}: invalid {field}")
    if any(part in row["source_module"] for part in FORBIDDEN_MODULE_PARTS):
        raise ValueError(f"{argument}: legacy five-check module is forbidden")
    source = Path(row["source_path"])
    receipt_path = Path(row["aggregate_receipt_path"])
    if (not source.is_absolute() or source.is_symlink() or not source.is_file()
            or source.name != row["source_module"].split(".")[-1] + ".lean"):
        raise ValueError(f"{argument}: source path/module mismatch")
    if sha256(source) != row["source_sha256"]:
        raise ValueError(f"{argument}: source hash mismatch")
    if (not receipt_path.is_absolute() or receipt_path.is_symlink()
            or not receipt_path.is_file()
            or sha256(receipt_path) != row["aggregate_receipt_sha256"]):
        raise ValueError(f"{argument}: aggregate receipt hash mismatch")
    receipt = json.loads(receipt_path.read_text())
    if singleton:
        expected = {"schema": RECEIPT_SCHEMA, "consumer_argument": argument,
                    "theorem": row["theorem"], "source_module": row["source_module"],
                    "source_sha256": row["source_sha256"]}
        if receipt != expected or receipt_path.read_bytes() != canonical_receipt(expected):
            raise ValueError(f"{argument}: receipt identity mismatch")
    return receipt


def expected_leaf_ids(cell: str) -> list[str]:
    return [f"{cell}.cover-left", f"{cell}.cover-right",
            *(f"{cell}.cube-{li}-{ri}" for li in range(7) for ri in range(8))]


def load_and_validate(path: Path, runner=None, before_return=None, _return_pins=False):
    _regular(path, "--inputs")
    pins = {path: _snapshot(path, "--inputs")}
    document = json.loads(path.read_text())
    document_fields = {"schema", "inputs", "cell_aggregate_index_path",
                       "cell_aggregate_index_sha256"}
    if not isinstance(document, dict) or set(document) != document_fields or document.get("schema") != SCHEMA:
        raise ValueError("unsupported seven-base wrapper input schema")
    rows = document.get("inputs")
    if not isinstance(rows, list) or len(rows) != 9:
        raise ValueError("inputs must contain exactly H1, seven bases, and H7")
    expected_arguments = ["h1", *(x[0] for x in SMALL_HIGH), "h7"]
    if [row.get("consumer_argument") for row in rows if isinstance(row, dict)] != expected_arguments:
        raise ValueError("inputs are missing, duplicated, or out of consumer order")
    initial_paths = []
    for row in rows:
        if not isinstance(row, dict): raise ValueError("input row malformed")
        for field in ("source_path", "aggregate_receipt_path"):
            target = Path(row.get(field, "")); initial_paths.append(target); pins[target] = _snapshot(target, field)
    index_initial = Path(document.get("cell_aggregate_index_path", "")); initial_paths.append(index_initial)
    pins[index_initial] = _snapshot(index_initial, "cell aggregate index")
    h1 = rows[0]
    if (set(h1) != CORE_FIELDS | {"final_receipt_path", "final_receipt_sha256"}
            or not SHA256.fullmatch(str(h1.get("final_receipt_sha256", "")))):
        raise ValueError("H1 row must bind exactly one final receipt")
    final_initial = Path(h1["final_receipt_path"]); initial_paths.append(final_initial)
    pins[final_initial] = _snapshot(final_initial, "h1 final receipt")
    identities = [(os.stat(target).st_dev, os.stat(target).st_ino) for target in initial_paths]
    allowed_small_source = (os.stat(Path(rows[1]["source_path"])).st_dev,
                            os.stat(Path(rows[1]["source_path"])).st_ino)
    duplicates = {identity: identities.count(identity) for identity in set(identities) if identities.count(identity) > 1}
    if duplicates not in ({}, {allowed_small_source: 7}): raise ValueError("provenance input paths alias")
    receipts = [_validate_core(row, argument, index in (0, 8))
                for index, (row, argument) in enumerate(
                    zip(rows, expected_arguments, strict=True))]
    identities = tuple((row["consumer_argument"], row["source_module"], row["theorem"])
                       for row in rows)
    if identities != EXPECTED_INPUTS:
        raise ValueError("the nine theorem/module identities do not match the pinned endpoints")
    for ordinal, (row, (argument, cell, theorem)) in enumerate(
            zip(rows[1:8], SMALL_HIGH, strict=True)):
        required = CORE_FIELDS | {"ordinal", "cell", "leaf_evidence_identity_sha256"}
        if set(row) != required:
            raise ValueError(f"{argument}: small-high row has wrong fields")
        if (row["ordinal"], row["cell"], row["theorem"]) != (ordinal, cell, theorem):
            raise ValueError(f"{argument}: small-high identity mismatch")
        if not SHA256.fullmatch(str(row["leaf_evidence_identity_sha256"])):
            raise ValueError(f"{argument}: invalid leaf evidence identity hash")
        receipt = receipts[ordinal + 1]
        receipt_fields = {"base_unsat_theorem", "cell", "consumer_argument",
            "expected_manifest_sha256", "leaf_count", "leaf_evidence_identity_sha256",
            "leaf_job_ids", "ordinal", "root_manifest_sha256", "schema",
            "socket_table_sha256", "socket_validator_identity_sha256",
            "source_module", "source_sha256"}
        if not isinstance(receipt, dict) or set(receipt) != receipt_fields:
            raise ValueError(f"{argument}: wrong cell aggregate receipt fields")
        if (receipt["schema"], receipt["ordinal"], receipt["consumer_argument"],
                receipt["cell"], receipt["base_unsat_theorem"], receipt["leaf_count"],
                receipt["source_module"], receipt["source_sha256"],
                receipt["leaf_evidence_identity_sha256"], receipt["leaf_job_ids"]) != (
                CELL_RECEIPT_SCHEMA, ordinal, argument, cell, theorem, 58,
                row["source_module"], row["source_sha256"],
                row["leaf_evidence_identity_sha256"], expected_leaf_ids(cell)):
            raise ValueError(f"{argument}: cell aggregate receipt identity mismatch")
        for field in ("expected_manifest_sha256", "root_manifest_sha256",
                      "socket_table_sha256", "socket_validator_identity_sha256"):
            if not isinstance(receipt[field], str) or not SHA256.fullmatch(receipt[field]):
                raise ValueError(f"{argument}: invalid aggregate global pin {field}")
        if Path(row["aggregate_receipt_path"]).read_bytes() != canonical_receipt(receipt):
            raise ValueError(f"{argument}: cell receipt bytes are not canonical")
    small_modules = {row["source_module"] for row in rows[1:8]}
    small_paths = {row["source_path"] for row in rows[1:8]}
    small_hashes = {row["source_sha256"] for row in rows[1:8]}
    if len(small_modules) != 1 or len(small_paths) != 1 or len(small_hashes) != 1:
        raise ValueError("the seven bases must come from one generated source")
    if set(rows[8]) != CORE_FIELDS:
        raise ValueError("H7 row must contain exactly the singleton provenance fields")
    _validate_h1_final(rows[0], pins, runner)
    receipt_hashes = [row["aggregate_receipt_sha256"] for row in rows]
    if len(set(receipt_hashes)) != 9:
        raise ValueError("all nine aggregate receipts must be distinct")
    leaf_identities = [row["leaf_evidence_identity_sha256"] for row in rows[1:8]]
    if len(set(leaf_identities)) != 7:
        raise ValueError("all seven leaf socket identity hashes must be distinct")
    for field in ("expected_manifest_sha256", "root_manifest_sha256",
                  "socket_table_sha256", "socket_validator_identity_sha256"):
        if len({receipt[field] for receipt in receipts[1:8]}) != 1:
            raise ValueError(f"seven cell receipts disagree on {field}")
    index_path = Path(document["cell_aggregate_index_path"])
    index_pin = document["cell_aggregate_index_sha256"]
    if (not index_path.is_absolute() or index_path.is_symlink() or not index_path.is_file()
            or not isinstance(index_pin, str) or not SHA256.fullmatch(index_pin)
            or sha256(index_path) != index_pin):
        raise ValueError("invalid cell aggregate index path/hash")
    index = json.loads(index_path.read_text())
    index_fields = {"cells", "expected_manifest_sha256", "root_manifest_sha256",
        "schema", "socket_table_sha256", "socket_validator_identity_sha256",
        "source_module", "source_sha256"}
    if (not isinstance(index, dict) or set(index) != index_fields
            or index_path.read_bytes() != canonical_receipt(index)
            or index["schema"] != CELL_INDEX_SCHEMA):
        raise ValueError("invalid or noncanonical cell aggregate index")
    expected_cells = []
    for row, (_, cell, _) in zip(rows[1:8], SMALL_HIGH, strict=True):
        receipt_name = f"{cell}.receipt.json"
        expected_path = index_path.parent / receipt_name
        if Path(row["aggregate_receipt_path"]) != expected_path:
            raise ValueError(f"{cell}: row receipt is outside the indexed set")
        expected_cells.append({"cell": cell, "receipt": receipt_name,
                               "receipt_sha256": row["aggregate_receipt_sha256"]})
    if index["cells"] != expected_cells:
        raise ValueError("aggregate index does not bind the exact seven receipts")
    first = receipts[1]
    for field in ("expected_manifest_sha256", "root_manifest_sha256",
                  "socket_table_sha256", "socket_validator_identity_sha256",
                  "source_module", "source_sha256"):
        if index[field] != first[field]:
            raise ValueError(f"aggregate index disagrees on {field}")
    for target, pin in pins.items(): _recheck(target, pin, "provenance input")
    if before_return is not None: before_return()
    for target, pin in pins.items(): _recheck(target, pin, "provenance input")
    return (rows, pins) if _return_pins else rows


def render(rows: list[dict]) -> str:
    modules = list(dict.fromkeys(row["source_module"] for row in rows))
    theorems = [row["theorem"] for row in rows]
    lines = [*(f"import {module}" for module in modules),
             "import Proofs.Erdos85OrderFortyNineSmallHighCubeGridTerminal",
             "import Proofs.Erdos85FiniteDropWitnesses", "",
             "/-! GENERATED from nine reviewed provenance inputs; no legacy five-check frontier. -/",
             "", "namespace Erdos85", "",
             "theorem not_c4FreeMinDegreeWitness_fortyNine_seven_of_generatedSevenBaseCertificates :",
             "    ¬ C4FreeMinDegreeWitness 49 7 :=",
             "  not_c4FreeMinDegreeWitness_fortyNine_seven_of_smallHighCubeBaseUnsat"]
    lines.extend(f"    {theorem}" for theorem in theorems)
    lines.extend(["",
        "theorem minDegreeForC4_fortyEight_fortyNine_exact_of_generatedSevenBaseCertificates :",
        "    minDegreeForC4 48 = 8 ∧ minDegreeForC4 49 = 7 :=",
        "  minDegreeForC4_fortyEight_fortyNine_exact_checked",
        "    not_c4FreeMinDegreeWitness_fortyNine_seven_of_generatedSevenBaseCertificates", "",
        "theorem minDegreeForC4_fortyNine_lt_fortyEight_of_generatedSevenBaseCertificates :",
        "    minDegreeForC4 49 < minDegreeForC4 48 :=",
        "  minDegreeForC4_fortyNine_lt_fortyEight_checked",
        "    not_c4FreeMinDegreeWitness_fortyNine_seven_of_generatedSevenBaseCertificates", "",
        "end Erdos85", ""])
    return "\n".join(lines)


def atomic_create(path: Path, source: str) -> None:
    if path.exists() or path.is_symlink(): raise FileExistsError(path)
    if not path.is_absolute() or path.parent != path.parent.resolve(strict=True):
        raise ValueError("output must have a canonical absolute parent")
    cursor = path.parent
    while True:
        if cursor.is_symlink(): raise ValueError("output has symlink ancestry")
        if cursor.parent == cursor: break
        cursor = cursor.parent
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.tmp.{os.getpid()}")
    try:
        with temporary.open("x") as stream:
            stream.write(source)
            stream.flush()
            os.fsync(stream.fileno())
        os.link(temporary, path)
        directory_fd = os.open(path.parent, os.O_RDONLY)
        try:
            os.fsync(directory_fd)
        finally:
            os.close(directory_fd)
    finally:
        temporary.unlink(missing_ok=True)

def publish(inputs: Path, output: Path, runner=None, before_output=None) -> list[dict]:
    rows, pins = load_and_validate(inputs, runner=runner, _return_pins=True)
    source = render(rows)
    if before_output is not None: before_output()
    for target, pin in pins.items(): _recheck(target, pin, "provenance input")
    atomic_create(output, source)
    return rows


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--inputs", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    publish(args.inputs.resolve(), args.output.absolute())
    print(f"WROTE {args.output.resolve()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
