#!/usr/bin/env python3
"""Produce receipt evidence for a pinned, network-isolated cold H1 endpoint build."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import resource
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path, PurePosixPath

SCHEMA = "erdos85-h1-endpoint-cold-build-v1"
POST_SCHEMA = "erdos85-h1-leaf-module-evidence-receipt-v1"
EVIDENCE_SCHEMA = "erdos85-h1-committed-leaf-evidence-v1"
POST_PRODUCER_SHA256 = "170d81727b9d0c612c4a0af9507b751aea4011f52f129efb46bdde39a9b96d70"
CACHE_SCHEMA = "erdos85-h1-offline-dependency-cache-v1"
CACHE_RECEIPT_SCHEMA = "erdos85-h1-offline-dependency-cache-snapshot-receipt-v1"
CACHE_PRODUCER_PATH = "research/problems/erdos-85-wip-01/sat49/snapshot_h1_offline_dependency_cache.py"
CACHE_PRODUCER_SHA256 = "931a663376508e3937f8b370eafc04e8750d5a413154246dbd1c31364372dd17"
TOOLCHAIN_SCHEMA = "erdos85-h1-endpoint-cold-build-toolchain-v1"
IMAGE = "lean4-arm64@sha256:a5ca6c4e3328a1832d5f9b814ab7c1e35616903b3956341962a5b1a96fb6dff6"
MODULE = "Proofs.Generated.Erdos85OrderFortyNineOneHighCertificates"
THEOREM = "Erdos85.orderFortyNineStratumExcluded_one_of_generatedCertificates"
SOURCE = "proofs/Proofs/Generated/Erdos85OrderFortyNineOneHighCertificates.lean"
OLEAN = ".lake/build/lib/lean/Proofs/Generated/Erdos85OrderFortyNineOneHighCertificates.olean"
CONTROL_PATHS = ("proofs/lean-toolchain", "proofs/lakefile.toml", "proofs/lake-manifest.json")
LAKE_MANIFEST_FIELDS = {"fixedToolchain", "lakeDir", "name", "packages", "packagesDir", "version"}
LAKE_PACKAGE_FIELDS = {"configFile", "inherited", "inputRev", "manifestFile", "name", "rev",
                       "scope", "subDir", "type", "url"}
SHA = re.compile(r"[0-9a-f]{64}")
COMMIT = re.compile(r"[0-9a-f]{40}")
TAG = re.compile(r"[0-9a-f]{16}")
REVIEW = re.compile(r"[A-Za-z0-9][A-Za-z0-9._:/-]{0,127}")


def canonical(value):
    return (json.dumps(value, ensure_ascii=True, allow_nan=False, sort_keys=True,
                       separators=(",", ":")) + "\n").encode("ascii")


def sha(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def safe(path, label, kind="file", absent=False):
    if not path.is_absolute() or path != path.resolve(strict=False):
        raise ValueError(f"{label} must be canonical and absolute")
    current = path if path.exists() else path.parent
    while True:
        if current.is_symlink():
            raise ValueError(f"{label} has symlink ancestry")
        if current == current.parent:
            break
        current = current.parent
    if absent:
        if path.exists() or path.is_symlink() or not path.parent.is_dir():
            raise ValueError(f"{label} must be absent under an existing directory")
    elif kind == "file" and (not path.is_file() or path.is_symlink()):
        raise ValueError(f"{label} must be a regular file")
    elif kind == "dir" and (not path.is_dir() or path.is_symlink()):
        raise ValueError(f"{label} must be a directory")


def require(path, pin, label):
    safe(path, label)
    if not isinstance(pin, str) or SHA.fullmatch(pin) is None or sha(path) != pin:
        raise ValueError(f"{label} path/hash mismatch")


def read_json(path, pin, label):
    require(path, pin, label)
    raw = path.read_bytes()
    value = json.loads(raw)
    if not isinstance(value, dict) or raw != canonical(value):
        raise ValueError(f"{label} must be canonical JSON")
    return value


def read_pretty_json(path, pin, label):
    require(path, pin, label)
    raw = path.read_bytes(); value = json.loads(raw)
    if (not isinstance(value, dict)
            or raw != (json.dumps(value, indent=2, sort_keys=True) + "\n").encode("utf-8")):
        raise ValueError(f"{label} must be canonical pretty JSON")
    return value


def relative(value, label):
    if not isinstance(value, str) or not value or "\\" in value:
        raise ValueError(f"{label} must be relative")
    path = PurePosixPath(value)
    if path.is_absolute() or not path.parts or any(part in ("", ".", "..") for part in path.parts):
        raise ValueError(f"{label} must be a canonical relative path")
    if str(path) != value:
        raise ValueError(f"{label} is not normalized")
    return path


def normalize_url(value):
    if not isinstance(value, str):
        raise ValueError("package remote URL malformed")
    match = re.fullmatch(
        r"(?:https://github\.com/|git@github\.com:)([^/]+)/([^/]+?)(?:\.git)?/?", value
    )
    if match is None:
        raise ValueError("package remote URL is not canonical GitHub remote")
    return f"github.com/{match.group(1).lower()}/{match.group(2).lower()}"


def command(runner, kind, argv, cwd, stdout, stderr):
    result = runner(kind, argv, cwd, {}, stdout, stderr)
    fields = {"cumulative_children_maxrss_kb", "rc", "system_ns", "user_ns", "wall_ns"}
    if (not isinstance(result, dict) or set(result) != fields or result["rc"] != 0
            or any(type(result[key]) is not int or result[key] < 0 for key in fields)
            or result["wall_ns"] <= 0 or result["cumulative_children_maxrss_kb"] <= 0):
        raise ValueError(f"{kind} command failed or returned malformed metrics")
    for path, label in ((stdout, "stdout"), (stderr, "stderr")):
        safe(path, f"{kind} {label}")
    core = {"argv": argv, "cwd": str(cwd), "environment": {}, "kind": kind}
    return {**core, **result, "command_identity_sha256": hashlib.sha256(canonical(core)).hexdigest(),
            "stdout_path": f"logs/{kind}.stdout", "stdout_sha256": sha(stdout),
            "stdout_bytes": stdout.stat().st_size, "stderr_path": f"logs/{kind}.stderr",
            "stderr_sha256": sha(stderr), "stderr_bytes": stderr.stat().st_size}


def templates():
    container = ["{runtime}", "run", "--rm", "--pull=never", "--network=none", "--read-only",
                 "--cpus=8", "--memory=32g", "--pids-limit=4096", "--tmpfs",
                 "/tmp:rw,noexec,nosuid,size=2g", "-v", "{checkout}:/workspace:rw",
                 "-w", "/workspace/proofs", "{image}"]
    return {
        "clone": ["{git}", "clone", "--no-hardlinks", "--no-checkout", "{repo}", "{checkout}"],
        "checkout": ["{git}", "-C", "{checkout}", "checkout", "--detach", "{commit}"],
        "head": ["{git}", "-C", "{checkout}", "rev-parse", "HEAD"],
        "status": ["{git}", "-C", "{checkout}", "status", "--porcelain=v1", "--untracked-files=all"],
        "control_commit_oids": ["{git}", "-C", "{checkout}", "rev-parse",
            *["{commit}:" + path for path in CONTROL_PATHS]],
        "control_worktree_oids": ["{git}", "-C", "{checkout}", "hash-object", "--", *CONTROL_PATHS],
        "cache_producer_commit_oid": ["{git}", "-C", "{checkout}", "rev-parse",
                                      "{commit}:" + CACHE_PRODUCER_PATH],
        "cache_producer_worktree_oid": ["{git}", "-C", "{checkout}", "hash-object", "--",
                                        CACHE_PRODUCER_PATH],
        "status_after": ["{git}", "-C", "{checkout}", "status", "--porcelain=v1", "--untracked-files=all"],
        "tool_hashes": [*container[:-1], "--entrypoint", "/usr/bin/sha256sum", "{image}",
                        "/root/.elan/bin/lean", "/root/.elan/bin/lake"],
        "lean_version": [*container, "lean", "--version"],
        "lake_version": [*container, "lake", "--version"],
        "build": [*container, "lake", "build", MODULE],
    }


def expand(template, values):
    result = [token.format_map(values) for token in template]
    if any(not token for token in result):
        raise ValueError("empty expanded command argument")
    return result


def fsync_tree(root):
    for path in root.rglob("*"):
        if path.is_file():
            with path.open("rb") as stream: os.fsync(stream.fileno())
    directories = [path for path in root.rglob("*") if path.is_dir()]
    for directory in sorted(directories, key=lambda p: len(p.parts), reverse=True) + [root]:
        fd = os.open(directory, os.O_RDONLY)
        try: os.fsync(fd)
        finally: os.close(fd)


def scan_generated(root, base, path_key):
    safe(root, "Generated artifact root", kind="dir")
    rows = []
    for current, directories, files in os.walk(root, followlinks=False):
        parent = Path(current)
        for name in directories:
            path = parent / name
            if path.is_symlink() or not path.is_dir():
                raise ValueError("Generated artifact tree contains special/aliased directory")
        for name in files:
            path = parent / name
            safe(path, "Generated artifact tree file")
            rel = PurePosixPath(path.relative_to(base).as_posix())
            if rel.suffix not in (".olean", ".ilean"):
                continue
            if path.stat().st_size <= 0: raise ValueError("compiled Generated artifact is empty")
            rows.append({path_key: rel.as_posix(), "bytes": path.stat().st_size, "sha256": sha(path)})
    rows.sort(key=lambda row: row[path_key])
    return rows


def build(*, repo, source_commit, review_id, post_receipt, post_receipt_sha256,
          cache_receipt, cache_receipt_sha256, cache_manifest, cache_manifest_sha256,
          toolchain, toolchain_sha256,
          output, runner, before_receipt=None):
    producer = Path(__file__).resolve()
    safe(repo, "repository", kind="dir")
    safe(output, "output", absent=True)
    if COMMIT.fullmatch(source_commit) is None or REVIEW.fullmatch(review_id) is None:
        raise ValueError("source commit/review id malformed")
    post = read_json(post_receipt, post_receipt_sha256, "post-module receipt")
    post_fields = {"adapter_receipt_path", "adapter_receipt_sha256", "aggregate_layout_path",
        "aggregate_layout_sha256", "bank_receipt_path", "bank_receipt_sha256",
        "capacity_reindex_receipt_path", "capacity_reindex_receipt_sha256", "commit_object_oid",
        "endpoint_module", "endpoint_source_path", "endpoint_source_sha256", "endpoint_theorem",
        "evidence_path", "evidence_sha256", "generated_tree_identity_sha256", "leaf_count",
        "leaf_module_index_path", "leaf_module_index_sha256", "producer_path", "producer_sha256",
        "profile_counts", "repo", "review_id", "reviewed_commit", "schema"}
    post_hashes = ("adapter_receipt_sha256", "aggregate_layout_sha256", "bank_receipt_sha256",
        "capacity_reindex_receipt_sha256", "endpoint_source_sha256", "evidence_sha256",
        "generated_tree_identity_sha256", "leaf_module_index_sha256", "producer_sha256")
    if (set(post) != post_fields or post.get("schema") != POST_SCHEMA
            or post.get("reviewed_commit") != source_commit or post.get("commit_object_oid") != source_commit
            or post.get("review_id") != review_id or post.get("repo") != str(repo)
            or post.get("endpoint_module") != MODULE or post.get("endpoint_theorem") != THEOREM
            or post.get("endpoint_source_path") != SOURCE or post.get("leaf_count") != 13351
            or post.get("profile_counts") != [1485, 3617, 4717, 2693, 839]
            or post.get("evidence_path") != "leaf-evidence.json"
            or post.get("producer_sha256") != POST_PRODUCER_SHA256
            or any(SHA.fullmatch(str(post.get(key))) is None for key in post_hashes)):
        raise ValueError("post-module receipt contract mismatch")
    captured = [producer, post_receipt]
    for path_key, pin_key in (("adapter_receipt_path", "adapter_receipt_sha256"),
            ("aggregate_layout_path", "aggregate_layout_sha256"),
            ("bank_receipt_path", "bank_receipt_sha256"),
            ("capacity_reindex_receipt_path", "capacity_reindex_receipt_sha256"),
            ("leaf_module_index_path", "leaf_module_index_sha256"),
            ("producer_path", "producer_sha256")):
        path = Path(post[path_key]); require(path, post[pin_key], f"post-module {path_key}"); captured.append(path)
    evidence_rel = relative(post["evidence_path"], "post-module evidence path")
    evidence_path = post_receipt.parent / Path(*evidence_rel.parts)
    evidence = read_json(evidence_path, post["evidence_sha256"], "post-module evidence")
    evidence_fields = {"adapter_repo_path", "adapter_source_identity", "aggregate_layout_source_identity",
        "aggregate_tree_identity_sha256", "generated_tree_identity_sha256", "leaf_count",
        "leaf_tree_identity_sha256", "profile_counts", "review_id", "reviewed_commit", "rows", "schema"}
    identity_fields = {"blob_oid", "bytes", "repo_path", "sha256"}
    row_fields = {"capacity_local_index", "leaf_blob_oid", "leaf_repo_path", "leaf_source_bytes",
        "leaf_source_sha256", "ledger_path", "ledger_sha256", "packed_path", "packed_sha256",
        "profile", "replay_evidence_path", "replay_evidence_sha256", "tag"}
    identities = (evidence.get("adapter_source_identity"), evidence.get("aggregate_layout_source_identity"))
    if (set(evidence) != evidence_fields or evidence.get("schema") != EVIDENCE_SCHEMA
            or evidence.get("reviewed_commit") != source_commit or evidence.get("review_id") != review_id
            or evidence.get("leaf_count") != post["leaf_count"]
            or evidence.get("profile_counts") != post["profile_counts"]
            or evidence.get("generated_tree_identity_sha256") != post["generated_tree_identity_sha256"]
            or evidence.get("adapter_repo_path") != SOURCE
            or any(not isinstance(identity, dict) or set(identity) != identity_fields
                   or COMMIT.fullmatch(str(identity.get("blob_oid"))) is None
                   or type(identity.get("bytes")) is not int or identity["bytes"] <= 0
                   or SHA.fullmatch(str(identity.get("sha256"))) is None
                   or not isinstance(identity.get("repo_path"), str) for identity in identities)
            or evidence["adapter_source_identity"].get("repo_path") != SOURCE
            or evidence["adapter_source_identity"].get("sha256") != post["endpoint_source_sha256"]
            or any(SHA.fullmatch(str(evidence.get(key))) is None for key in
                   ("aggregate_tree_identity_sha256", "leaf_tree_identity_sha256"))
            or not isinstance(evidence.get("rows"), list) or len(evidence["rows"]) != post["leaf_count"]
            or any(not isinstance(row, dict) or set(row) != row_fields for row in evidence["rows"])):
        raise ValueError("post-module evidence contract mismatch")
    expected_coordinates = [(profile, local) for profile, count in enumerate(post["profile_counts"])
                            for local in range(count)]
    tags = set()
    for row, coordinate in zip(evidence["rows"], expected_coordinates, strict=True):
        path_keys = ("leaf_repo_path", "ledger_path", "packed_path", "replay_evidence_path")
        if ((row.get("profile"), row.get("capacity_local_index")) != coordinate
                or COMMIT.fullmatch(str(row.get("leaf_blob_oid"))) is None
                or type(row.get("leaf_source_bytes")) is not int or row["leaf_source_bytes"] <= 0
                or any(SHA.fullmatch(str(row.get(key))) is None for key in
                       ("leaf_source_sha256", "ledger_sha256", "packed_sha256", "replay_evidence_sha256"))
                or TAG.fullmatch(str(row.get("tag"))) is None or row["tag"] in tags):
            raise ValueError("post-module evidence ordered row contract mismatch")
        for key in path_keys: relative(row.get(key), f"post-module evidence row {key}")
        tags.add(row["tag"])
    relative(evidence["aggregate_layout_source_identity"]["repo_path"],
             "aggregate layout committed path")
    captured.append(evidence_path)
    layout_path = Path(post["aggregate_layout_path"])
    layout = read_pretty_json(layout_path, post["aggregate_layout_sha256"], "aggregate layout")
    layout_fields = {"bank_size", "inputs", "inventory_contract", "leaf_count", "leaf_members_sha256",
        "modules", "prefixes", "profile_bank_counts", "schema", "top_module"}
    layout_module_fields = {"direct_import_count", "direct_imports", "file", "kind", "members", "module",
                            "source_bytes", "source_sha256", "theorem"}
    if (set(layout) != layout_fields or layout.get("schema") != "erdos85-h1-v2-aggregate-layout-v1"
            or layout.get("leaf_count") != post["leaf_count"] or not isinstance(layout.get("modules"), list)
            or not layout["modules"] or any(not isinstance(item, dict) or set(item) != layout_module_fields
                                             for item in layout["modules"])):
        raise ValueError("aggregate layout contract mismatch")
    generated_sources = [row["leaf_repo_path"] for row in evidence["rows"]]
    for item in layout["modules"]:
        generated_sources.append("proofs/" + "/".join(item["module"].split(".")) + ".lean")
    generated_sources.append(SOURCE)
    expected_oleans = set()
    for source_path in generated_sources:
        source_rel = relative(source_path, "generated source path")
        if source_rel.parts[:3] != ("proofs", "Proofs", "Generated") or source_rel.suffix != ".lean":
            raise ValueError("generated source path is outside exact Generated Lean namespace")
        expected_oleans.add(PurePosixPath(".lake/build/lib/lean", *source_rel.parts[1:]).with_suffix(".olean"))
    cache_snapshot = read_json(cache_receipt, cache_receipt_sha256,
                               "dependency-cache snapshot receipt")
    cache_receipt_fields = {"cache_manifest_path", "cache_manifest_sha256", "control_files",
        "entry_count", "git_path", "git_sha256", "package_count", "packages",
        "producer_path", "producer_sha256", "repo", "schema", "source_commit"}
    cache_producer = repo / Path(*PurePosixPath(CACHE_PRODUCER_PATH).parts)
    if (set(cache_snapshot) != cache_receipt_fields
            or cache_snapshot.get("schema") != CACHE_RECEIPT_SCHEMA
            or cache_snapshot.get("source_commit") != source_commit
            or cache_snapshot.get("repo") != str(repo)
            or cache_snapshot.get("producer_path") != str(cache_producer)
            or cache_snapshot.get("producer_sha256") != CACHE_PRODUCER_SHA256
            or cache_snapshot.get("cache_manifest_sha256") != cache_manifest_sha256
            or type(cache_snapshot.get("entry_count")) is not int
            or cache_snapshot["entry_count"] < 0
            or type(cache_snapshot.get("package_count")) is not int
            or cache_snapshot["package_count"] < 0):
        raise ValueError("dependency-cache snapshot receipt contract mismatch")
    require(cache_producer, CACHE_PRODUCER_SHA256, "dependency-cache snapshot producer")
    cache_manifest_rel = relative(cache_snapshot["cache_manifest_path"],
                                  "dependency-cache snapshot manifest path")
    if cache_manifest_rel.as_posix() != "cache-manifest.json":
        raise ValueError("dependency-cache snapshot manifest path mismatch")
    resolved_cache_manifest = cache_receipt.parent / Path(*cache_manifest_rel.parts)
    if cache_manifest != resolved_cache_manifest:
        raise ValueError("dependency-cache manifest path differs from snapshot receipt")
    controls = cache_snapshot["control_files"]
    if (not isinstance(controls, list) or len(controls) != len(CONTROL_PATHS)
            or [item.get("path") if isinstance(item, dict) else None for item in controls]
               != list(CONTROL_PATHS)):
        raise ValueError("dependency-cache snapshot control identities malformed")
    for item in controls:
        if (set(item) != {"blob_oid", "bytes", "path", "sha256"}
                or COMMIT.fullmatch(str(item["blob_oid"])) is None
                or type(item["bytes"]) is not int or item["bytes"] <= 0
                or SHA.fullmatch(str(item["sha256"])) is None):
            raise ValueError("dependency-cache snapshot control identities malformed")
    packages = cache_snapshot["packages"]
    package_fields = {"head", "manifest_url", "name", "normalized_remote", "path", "rev",
                      "source_identity_sha256"}
    if (not isinstance(packages, list) or len(packages) != cache_snapshot["package_count"]):
        raise ValueError("dependency-cache snapshot package identities malformed")
    package_names, normalized_remotes = set(), set()
    for item in packages:
        if (not isinstance(item, dict) or set(item) != package_fields
                or not isinstance(item["name"], str)
                or re.fullmatch(r"[A-Za-z][A-Za-z0-9_-]*", item["name"]) is None
                or item["name"] in package_names
                or COMMIT.fullmatch(str(item["head"])) is None or item["head"] != item["rev"]
                or SHA.fullmatch(str(item["source_identity_sha256"])) is None
                or not all(isinstance(item[key], str) and item[key]
                           for key in ("manifest_url", "normalized_remote", "path"))):
            raise ValueError("dependency-cache snapshot package identities malformed")
        expected_package_path = repo / "proofs/.lake/packages" / item["name"]
        if (item["path"] != str(expected_package_path)
                or item["normalized_remote"] != normalize_url(item["manifest_url"])
                or item["normalized_remote"] in normalized_remotes):
            raise ValueError("dependency-cache snapshot package identities malformed")
        package_names.add(item["name"])
        normalized_remotes.add(item["normalized_remote"])
    cache = read_json(cache_manifest, cache_manifest_sha256, "dependency-cache manifest")
    if set(cache) != {"entries", "identity_sha256", "root", "schema"} or cache.get("schema") != CACHE_SCHEMA:
        raise ValueError("dependency-cache manifest schema mismatch")
    cache_root = Path(cache["root"]); safe(cache_root, "dependency-cache root", kind="dir")
    if cache_root != cache_receipt.parent / "cache":
        raise ValueError("dependency-cache root differs from snapshot receipt")
    if not isinstance(cache.get("entries"), list): raise ValueError("cache entries malformed")
    entries, seen = [], set()
    for item in cache["entries"]:
        if (not isinstance(item, dict) or set(item) != {"bytes", "path", "sha256"}
                or type(item["bytes"]) is not int or item["bytes"] < 0 or SHA.fullmatch(str(item["sha256"])) is None):
            raise ValueError("cache entry malformed")
        rel = relative(item["path"], "cache entry")
        if rel.parts[0] != ".lake" or item["path"] in seen: raise ValueError("cache path/duplicate mismatch")
        generated_prefix = (".lake", "build", "lib", "lean", "Proofs", "Generated")
        if rel.parts[:len(generated_prefix)] == generated_prefix and rel.suffix in (".olean", ".ilean"):
            raise ValueError("dependency cache contains generated-tree Lean artifact")
        seen.add(item["path"]); source = cache_root / Path(*rel.parts)
        require(source, item["sha256"], "cache entry")
        if source.stat().st_size != item["bytes"]: raise ValueError("cache entry byte mismatch")
        captured.append(source); entries.append((source, item))
    cache_identity = hashlib.sha256(canonical(cache["entries"])).hexdigest()
    if [item["path"] for item in cache["entries"]] != sorted(item["path"] for item in cache["entries"]):
        raise ValueError("cache entries are not in canonical path order")
    if cache_identity != cache["identity_sha256"]: raise ValueError("cache identity mismatch")
    if cache_snapshot["entry_count"] != len(cache["entries"]):
        raise ValueError("dependency-cache snapshot entry count mismatch")
    observed_package_names = {PurePosixPath(item["path"]).parts[2] for item in cache["entries"]
        if PurePosixPath(item["path"]).parts[:2] == (".lake", "packages")
        and len(PurePosixPath(item["path"]).parts) >= 3}
    if observed_package_names != package_names:
        raise ValueError("dependency-cache snapshot package set mismatch")
    for package in packages:
        package_entries = [item for item in cache["entries"]
            if PurePosixPath(item["path"]).parts[:3] == (".lake", "packages", package["name"])]
        expected_identity = hashlib.sha256(canonical(package_entries)).hexdigest()
        if not package_entries or package["source_identity_sha256"] != expected_identity:
            raise ValueError("dependency-cache snapshot package source identity mismatch")
    tools = read_json(toolchain, toolchain_sha256, "cold-build toolchain")
    tool_fields = {"command_identity_derivation", "command_templates", "container_runtime_path",
                   "container_runtime_sha256", "git_path", "git_sha256", "image", "resource_policy", "schema"}
    policy = {"cpus": 8, "memory": "32g", "network": "none", "pids_limit": 4096,
              "read_only_container": True, "tmpfs": "/tmp:rw,noexec,nosuid,size=2g"}
    if (set(tools) != tool_fields or tools.get("schema") != TOOLCHAIN_SCHEMA or tools.get("image") != IMAGE
            or tools.get("command_templates") != templates() or tools.get("resource_policy") != policy
            or tools.get("command_identity_derivation") != "sha256(canonical-json({argv,cwd,environment,kind}))"):
        raise ValueError("cold-build toolchain contract mismatch")
    git = Path(tools["git_path"]); runtime = Path(tools["container_runtime_path"])
    require(git, tools["git_sha256"], "git executable")
    require(runtime, tools["container_runtime_sha256"], "container runtime")
    if (cache_snapshot["git_path"] != str(git)
            or cache_snapshot["git_sha256"] != tools["git_sha256"]):
        raise ValueError("dependency-cache snapshot Git identity mismatch")
    captured.extend((cache_receipt, cache_producer, cache_manifest, toolchain, git, runtime))
    pins = {str(producer): sha(producer), str(post_receipt): post_receipt_sha256,
            str(evidence_path): post["evidence_sha256"], str(cache_receipt): cache_receipt_sha256,
            str(cache_producer): CACHE_PRODUCER_SHA256, str(cache_manifest): cache_manifest_sha256,
            str(toolchain): toolchain_sha256, str(git): tools["git_sha256"],
            str(runtime): tools["container_runtime_sha256"]}
    for path_key, pin_key in (("adapter_receipt_path", "adapter_receipt_sha256"),
            ("aggregate_layout_path", "aggregate_layout_sha256"), ("bank_receipt_path", "bank_receipt_sha256"),
            ("capacity_reindex_receipt_path", "capacity_reindex_receipt_sha256"),
            ("leaf_module_index_path", "leaf_module_index_sha256"), ("producer_path", "producer_sha256")):
        pins[str(Path(post[path_key]))] = post[pin_key]
    for cache_source, item in entries: pins[str(cache_source)] = item["sha256"]
    stage = Path(tempfile.mkdtemp(prefix=".h1-cold-build-stage.", dir=output.parent))
    try:
        checkout, logs, publication = stage / "checkout", stage / "logs", stage / "publication"
        logs.mkdir(); publication.mkdir()
        values = {"checkout": str(checkout), "commit": source_commit, "git": str(git),
                  "image": IMAGE, "repo": str(repo), "runtime": str(runtime)}
        records = {}
        def invoke(kind, cwd):
            stdout, stderr = logs / f"{kind}.stdout", logs / f"{kind}.stderr"
            records[kind] = command(runner, kind, expand(tools["command_templates"][kind], values),
                                    cwd, stdout, stderr)
        invoke("clone", stage)
        safe(checkout, "fresh checkout", kind="dir"); safe(checkout / ".git", "fresh checkout git dir", kind="dir")
        invoke("checkout", stage); invoke("head", stage); invoke("status", stage)
        invoke("control_commit_oids", stage); invoke("control_worktree_oids", stage)
        invoke("cache_producer_commit_oid", stage); invoke("cache_producer_worktree_oid", stage)
        if (logs / "head.stdout").read_text() != source_commit + "\n" or (logs / "status.stdout").read_bytes() != b"":
            raise ValueError("fresh checkout identity/status mismatch")
        commit_oids = (logs / "control_commit_oids.stdout").read_text().splitlines()
        worktree_oids = (logs / "control_worktree_oids.stdout").read_text().splitlines()
        if (len(commit_oids) != len(CONTROL_PATHS) or commit_oids != worktree_oids
                or any(COMMIT.fullmatch(oid) is None for oid in commit_oids)):
            raise ValueError("reviewed control file Git identity mismatch")
        control_identities = []
        for repo_path, blob_oid in zip(CONTROL_PATHS, commit_oids, strict=True):
            path = checkout / Path(*PurePosixPath(repo_path).parts); safe(path, f"reviewed {repo_path}")
            if path.stat().st_size <= 0: raise ValueError(f"reviewed {repo_path} is empty")
            control_identities.append({"blob_oid": blob_oid, "bytes": path.stat().st_size,
                                       "path": repo_path, "sha256": sha(path)})
        if control_identities != controls:
            raise ValueError("dependency-cache snapshot control identity mismatch")
        cache_producer_commit_oids = (logs / "cache_producer_commit_oid.stdout").read_text().splitlines()
        cache_producer_worktree_oids = (logs / "cache_producer_worktree_oid.stdout").read_text().splitlines()
        if (len(cache_producer_commit_oids) != 1
                or cache_producer_commit_oids != cache_producer_worktree_oids
                or COMMIT.fullmatch(cache_producer_commit_oids[0]) is None):
            raise ValueError("dependency-cache snapshot producer Git identity mismatch")
        checkout_cache_producer = checkout / Path(*PurePosixPath(CACHE_PRODUCER_PATH).parts)
        require(checkout_cache_producer, CACHE_PRODUCER_SHA256,
                "committed dependency-cache snapshot producer")
        cache_producer_identity = {"blob_oid": cache_producer_commit_oids[0],
            "bytes": checkout_cache_producer.stat().st_size, "path": CACHE_PRODUCER_PATH,
            "sha256": CACHE_PRODUCER_SHA256}
        manifest_path = checkout / "proofs/lake-manifest.json"
        try:
            lake_manifest = json.loads(manifest_path.read_bytes())
        except (OSError, json.JSONDecodeError) as error:
            raise ValueError("committed Lake manifest malformed") from error
        manifest_packages = lake_manifest.get("packages") if isinstance(lake_manifest, dict) else None
        if (not isinstance(lake_manifest, dict) or set(lake_manifest) != LAKE_MANIFEST_FIELDS
                or lake_manifest.get("version") != "1.2.0"
                or lake_manifest.get("packagesDir") != ".lake/packages"
                or lake_manifest.get("lakeDir") != ".lake" or lake_manifest.get("name") != "proofs"
                or not isinstance(manifest_packages, list)
                or any(not isinstance(item, dict) or set(item) != LAKE_PACKAGE_FIELDS
                       or item.get("type") != "git" or item.get("subDir") is not None
                       or COMMIT.fullmatch(str(item.get("rev"))) is None
                       for item in manifest_packages)):
            raise ValueError("committed Lake manifest schema mismatch")
        expected_package_provenance = [(item["name"], item["rev"], item["url"])
                                       for item in manifest_packages]
        observed_package_provenance = [(item["name"], item["rev"], item["manifest_url"])
                                       for item in packages]
        if observed_package_provenance != expected_package_provenance:
            raise ValueError("dependency-cache snapshot package manifest provenance mismatch")
        source = checkout / Path(*PurePosixPath(SOURCE).parts)
        require(source, post["endpoint_source_sha256"], "committed endpoint source")
        source_raw = source.read_bytes().lower()
        if re.search(rb"\b(sorry|admit)\b", source_raw): raise ValueError("endpoint source contains sorry/admit")
        proofs = checkout / "proofs"
        lake_root = proofs / ".lake"
        if lake_root.exists() or lake_root.is_symlink(): raise ValueError("checkout inherited .lake")
        for cache_source, item in entries:
            destination = proofs / Path(*PurePosixPath(item["path"]).parts)
            if destination.exists() or destination.is_symlink(): raise ValueError("checkout inherited cache entry")
            destination.parent.mkdir(parents=True, exist_ok=True); shutil.copyfile(cache_source, destination)
            require(destination, item["sha256"], "staged dependency cache entry")
            if destination.stat().st_size != item["bytes"]: raise ValueError("staged cache entry byte mismatch")
        staged_cache_files = {str(path.relative_to(proofs).as_posix()) for path in lake_root.rglob("*") if path.is_file()}
        if staged_cache_files != {item["path"] for _, item in entries}:
            raise ValueError("staged dependency cache file set mismatch")
        target = proofs / Path(*PurePosixPath(OLEAN).parts)
        if target.exists() or target.is_symlink(): raise ValueError("target olean exists before cold build")
        invoke("tool_hashes", stage); invoke("lean_version", stage); invoke("lake_version", stage); invoke("build", stage)
        invoke("status_after", stage)
        if (logs / "status_after.stdout").read_bytes() != b"":
            raise ValueError("committed source tree changed during build")
        safe(target, "target olean")
        if target.stat().st_size <= 0: raise ValueError("target olean is empty")
        generated_root = lake_root / "build/lib/lean/Proofs/Generated"
        safe(generated_root, "compiled Generated root", kind="dir")
        source_rows = scan_generated(generated_root, proofs, "build_path")
        observed_oleans = set()
        for row in source_rows:
            rel = PurePosixPath(row["build_path"])
            corresponding_olean = rel.with_suffix(".olean")
            if corresponding_olean not in expected_oleans:
                raise ValueError("unexpected compiled Generated artifact")
            if rel.suffix == ".olean": observed_oleans.add(rel)
        if observed_oleans != expected_oleans:
            raise ValueError("compiled Generated olean cone mismatch")
        tool_lines = (logs / "tool_hashes.stdout").read_text().splitlines()
        if len(tool_lines) != 2 or any(re.fullmatch(r"[0-9a-f]{64}  /root/\.elan/bin/(lean|lake)", line) is None
                                      for line in tool_lines):
            raise ValueError("container tool hash evidence malformed")
        if not (logs / "lean_version.stdout").read_text().startswith("Lean (version 4.31.0"):
            raise ValueError("Lean version mismatch")
        if not (logs / "lake_version.stdout").read_text().startswith("Lake version 5.0.0"):
            raise ValueError("Lake version mismatch")
        for path in sorted(logs.iterdir()):
            destination = publication / "logs" / path.name; destination.parent.mkdir(exist_ok=True)
            shutil.copyfile(path, destination)
        retained_olean = publication / "artifacts" / "endpoint.olean"
        retained_olean.parent.mkdir(); shutil.copyfile(target, retained_olean)
        compiled_rows = []
        for row in source_rows:
            rel = PurePosixPath(row["build_path"]); source_path = proofs / Path(*rel.parts)
            source_bytes, source_sha = row["bytes"], row["sha256"]
            artifact_rel = PurePosixPath("artifacts/generated", *rel.parts[4:])
            destination = publication / Path(*artifact_rel.parts); destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source_path, destination); safe(destination, "retained Generated artifact")
            if (sha(source_path) != source_sha or source_path.stat().st_size != source_bytes
                    or sha(destination) != source_sha or destination.stat().st_size != source_bytes):
                raise ValueError("retained Generated artifact copy mismatch")
            compiled_rows.append({"artifact_path": artifact_rel.as_posix(), "build_path": rel.as_posix(),
                                  "bytes": source_bytes, "sha256": source_sha})
        endpoint_rows = [row for row in compiled_rows if row["build_path"] == OLEAN]
        if (len(endpoint_rows) != 1 or endpoint_rows[0]["bytes"] != target.stat().st_size
                or endpoint_rows[0]["sha256"] != sha(target)):
            raise ValueError("generated endpoint/target olean crosslink mismatch")
        receipt = {"cache_identity_sha256": cache_identity, "cache_manifest_path": str(cache_manifest),
            "cache_manifest_sha256": cache_manifest_sha256, "commands": records,
            "cache_snapshot_producer_sha256": CACHE_PRODUCER_SHA256,
            "cache_snapshot_producer_identity": cache_producer_identity,
            "cache_snapshot_receipt_path": str(cache_receipt),
            "cache_snapshot_receipt_sha256": cache_receipt_sha256,
            "endpoint_module": MODULE, "endpoint_source_path": SOURCE,
            "endpoint_source_sha256": post["endpoint_source_sha256"], "endpoint_theorem": THEOREM,
            "generated_tree_identity_sha256": post["generated_tree_identity_sha256"], "image": IMAGE,
            "retained_generated_artifacts": compiled_rows,
            "post_module_receipt_path": str(post_receipt), "post_module_receipt_sha256": post_receipt_sha256,
            "producer_path": str(producer), "producer_sha256": pins[str(producer)], "resource_policy": policy,
            "reviewed_control_files": control_identities,
            "review_id": review_id, "schema": SCHEMA, "source_commit": source_commit,
            "target_olean_build_path": OLEAN, "target_olean_bytes": target.stat().st_size,
            "target_generated_artifact_path": endpoint_rows[0]["artifact_path"],
            "target_olean_path": "artifacts/endpoint.olean",
            "target_olean_sha256": sha(target), "toolchain_path": str(toolchain),
            "toolchain_sha256": toolchain_sha256}
        for path in sorted((publication / "logs").iterdir()):
            with path.open("rb") as stream: os.fsync(stream.fileno())
        if before_receipt is not None: before_receipt()
        for path, pin in pins.items():
            try: require(Path(path), pin, "captured input")
            except ValueError as error: raise ValueError("input drift before receipt") from error
        require(checkout_cache_producer, cache_producer_identity["sha256"],
                "committed dependency-cache snapshot producer drift before receipt")
        if checkout_cache_producer.stat().st_size != cache_producer_identity["bytes"]:
            raise ValueError("committed dependency-cache snapshot producer drift before receipt")
        safe(repo, "repository", kind="dir"); safe(output.parent, "output parent", kind="dir")
        require(source, post["endpoint_source_sha256"], "committed endpoint source")
        for identity in control_identities:
            path = checkout / Path(*PurePosixPath(identity["path"]).parts)
            require(path, identity["sha256"], f"reviewed {identity['path']}")
            if path.stat().st_size != identity["bytes"]: raise ValueError("reviewed control file drift")
        if sha(target) != receipt["target_olean_sha256"] or target.stat().st_size != receipt["target_olean_bytes"]:
            raise ValueError("target olean drift before receipt")
        if sha(retained_olean) != receipt["target_olean_sha256"] \
                or retained_olean.stat().st_size != receipt["target_olean_bytes"]:
            raise ValueError("retained target olean drift before receipt")
        for row in compiled_rows:
            source_path = proofs / Path(*PurePosixPath(row["build_path"]).parts)
            retained = publication / Path(*PurePosixPath(row["artifact_path"]).parts)
            for path in (source_path, retained):
                require(path, row["sha256"], "Generated artifact drift before receipt")
                if path.stat().st_size != row["bytes"]: raise ValueError("Generated artifact byte drift")
        final_source_rows = scan_generated(generated_root, proofs, "build_path")
        expected_source_rows = [{key: row[key] for key in ("build_path", "bytes", "sha256")}
                                for row in compiled_rows]
        if final_source_rows != expected_source_rows:
            raise ValueError("Generated source artifact set drift before receipt")
        retained_rows = scan_generated(publication / "artifacts/generated", publication, "artifact_path")
        expected_retained_rows = [{key: row[key] for key in ("artifact_path", "bytes", "sha256")}
                                  for row in compiled_rows]
        if retained_rows != expected_retained_rows:
            raise ValueError("retained Generated artifact set drift before receipt")
        for record in records.values():
            for stream in ("stdout", "stderr"):
                retained = publication / record[f"{stream}_path"]
                if sha(retained) != record[f"{stream}_sha256"] or retained.stat().st_size != record[f"{stream}_bytes"]:
                    raise ValueError("retained command log drift")
        (publication / "receipt.json").write_bytes(canonical(receipt))
        with (publication / "receipt.json").open("rb") as stream: os.fsync(stream.fileno())
        fsync_tree(publication)
        if output.exists() or output.is_symlink(): raise ValueError("output appeared before publication")
        publication.rename(output)
        fd = os.open(output.parent, os.O_RDONLY)
        try: os.fsync(fd)
        finally: os.close(fd)
        return receipt
    except Exception:
        if stage.exists(): shutil.rmtree(stage)
        raise
    finally:
        if stage.exists(): shutil.rmtree(stage)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True); parser.add_argument("--source-commit", required=True)
    parser.add_argument("--review-id", required=True)
    for name in ("post-receipt", "cache-receipt", "cache-manifest", "toolchain"):
        parser.add_argument(f"--{name}", type=Path, required=True); parser.add_argument(f"--{name}-sha256", required=True)
    parser.add_argument("--output", type=Path, required=True); args = parser.parse_args()
    def runner(kind, argv, cwd, environment, stdout, stderr):
        before = resource.getrusage(resource.RUSAGE_CHILDREN); started = time.monotonic_ns()
        with stdout.open("xb") as out, stderr.open("xb") as err:
            result = subprocess.run(argv, cwd=cwd, env=environment, stdout=out, stderr=err)
            out.flush(); err.flush(); os.fsync(out.fileno()); os.fsync(err.fileno())
        after = resource.getrusage(resource.RUSAGE_CHILDREN)
        return {"cumulative_children_maxrss_kb": max(1, int(after.ru_maxrss)), "rc": result.returncode,
                "system_ns": max(0, int((after.ru_stime-before.ru_stime)*1_000_000_000)),
                "user_ns": max(0, int((after.ru_utime-before.ru_utime)*1_000_000_000)),
                "wall_ns": max(1, time.monotonic_ns()-started)}
    build(repo=args.repo, source_commit=args.source_commit, review_id=args.review_id,
          post_receipt=args.post_receipt, post_receipt_sha256=args.post_receipt_sha256,
          cache_receipt=args.cache_receipt, cache_receipt_sha256=args.cache_receipt_sha256,
          cache_manifest=args.cache_manifest, cache_manifest_sha256=args.cache_manifest_sha256,
          toolchain=args.toolchain, toolchain_sha256=args.toolchain_sha256,
          output=args.output, runner=runner)


if __name__ == "__main__": main()
