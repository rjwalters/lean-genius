#!/usr/bin/env python3
"""Create an immutable, ordered snapshot of terminal H1 capacity ledgers."""

from __future__ import annotations

import argparse
import csv
import hashlib
import importlib.util
import json
import os
import re
import shutil
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
SCHEMA = "erdos85-h1-capacity-selected-ledgers-v1"
RECEIPT_SCHEMA = "erdos85-h1-capacity-selected-ledgers-receipt-v1"
COVERAGE_SCHEMA = "erdos85-h1-coverage-audit-snapshot-v1"
PROFILE_COUNTS = (1485, 3617, 4717, 2693, 839)
PROFILE_NAMES = ("BBBB", "ABBB", "AABB", "AAAB", "AAAA")
SHA = re.compile(r"[0-9a-f]{64}")
TAG = re.compile(r"[0-9a-f]{16}")
STAMP = re.compile(r"\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z")
NODE = re.compile(r"i-[0-9a-f]+")
COVERAGE_HEADER = (
    "tag", "profile", "family", "local_index", "inventory_source", "status",
    "certified_s3", "host_unsat", "host_cnf_sha256", "host_verdict",
    "fleet_claim", "fleet_cnf_sha256", "fleet_verdict", "cnf_sha_divergent",
    "fleet_v2_claim", "fleet_v2_cnf_sha256", "fleet_v2_verdict",
    "fleet_v3_claim", "fleet_v3_cnf_sha256", "fleet_v3_verdict",
)
COMMON_KEYS = (
    "p", "i", "rc", "emit_s", "solve_s", "trim_s", "cap_s", "cnf_sha256",
    "cnf_clauses", "drat_bytes", "trim", "raw_lrat_sha256", "raw_lrat_bytes",
    "compact", "compact_lrat_sha256", "compact_bytes", "compact_gz_sha256", "upload",
)
CERTIFICATE_KEYS = (
    "p", "i", "cnf_sha256", "cnf_clauses", "raw_lrat_sha256", "raw_lrat_bytes",
    "compact_lrat_sha256", "compact_bytes", "compact_gz_sha256",
)


def canonical(value: object) -> bytes:
    return (json.dumps(value, ensure_ascii=True, allow_nan=False, sort_keys=True,
                       separators=(",", ":")) + "\n").encode("ascii")


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def safe_path(path: Path, label: str, kind: str = "file", absent: bool = False) -> None:
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


def require_file(path: Path, pin: str, label: str) -> None:
    safe_path(path, label)
    if not isinstance(pin, str) or SHA.fullmatch(pin) is None or sha256(path) != pin:
        raise ValueError(f"{label} hash mismatch")


def read_json(path: Path, pin: str, label: str) -> dict:
    require_file(path, pin, label)
    raw = path.read_bytes()
    value = json.loads(raw)
    if not isinstance(value, dict) or raw != canonical(value):
        raise ValueError(f"{label} must be canonical JSON")
    return value


def load_filter():
    spec = importlib.util.spec_from_file_location("h1_capacity_filter", HERE / "filter_h1_capacity_inventory.py")
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


def inventory_rows(path: Path, counts: tuple[int, ...]) -> list[dict]:
    worker_tag = load_filter().worker_tag
    rows, local = [], [0] * 5
    for number, raw in enumerate(path.read_text(encoding="ascii").splitlines(), 1):
        fields = raw.split()
        try:
            profile, *values = map(int, fields)
        except ValueError as error:
            raise ValueError(f"capacity inventory row {number} malformed") from error
        if profile not in range(5) or len(values) != 24 or any(value not in range(5) for value in values):
            raise ValueError(f"capacity inventory row {number} malformed")
        tag = worker_tag(tuple(values))
        rows.append({"tag": tag, "profile": profile, "local_index": local[profile]})
        local[profile] += 1
    if tuple(local) != tuple(counts) or len({row["tag"] for row in rows}) != len(rows):
        raise ValueError("capacity inventory ordering/counts mismatch")
    return rows


def inventory_universe(path: Path) -> dict[str, int]:
    worker_tag = load_filter().worker_tag
    result = {}
    for number, raw in enumerate(path.read_text(encoding="ascii").splitlines(), 1):
        try:
            profile, *values = map(int, raw.split())
        except ValueError as error:
            raise ValueError(f"raw inventory row {number} malformed") from error
        if profile not in range(5) or len(values) != 24 or any(value not in range(5) for value in values):
            raise ValueError(f"raw inventory row {number} malformed")
        tag = worker_tag(tuple(values))
        if tag in result:
            raise ValueError("raw inventory has duplicate tag")
        result[tag] = profile
    return result


def read_manifest(path: Path, source: str) -> dict[str, dict]:
    raw = path.read_bytes()
    if not raw.endswith(b"\n") or b"\r" in raw:
        raise ValueError(f"{source} manifest is not canonical newline-terminated ASCII")
    try:
        lines = raw.decode("ascii").splitlines()
    except UnicodeDecodeError as error:
        raise ValueError(f"{source} manifest is not ASCII") from error
    result, locals_ = {}, [0] * 5
    previous_tags = [""] * 5
    previous_profile = -1
    worker_tag = load_filter().worker_tag
    for number, line in enumerate(lines, 1):
        fields = line.split("\t")
        if len(fields) != 5 or not TAG.fullmatch(fields[0]):
            raise ValueError(f"{source} manifest row {number} malformed")
        tag, profile_raw, family, index_raw, values_raw = fields
        try:
            profile, index = int(profile_raw), int(index_raw)
            values = tuple(map(int, values_raw.split(" ")))
        except ValueError as error:
            raise ValueError(f"{source} manifest row {number} malformed") from error
        if (profile not in range(5) or family != PROFILE_NAMES[profile] or index != locals_[profile]
                or len(values) != 24 or any(value not in range(5) for value in values)
                or profile < previous_profile or worker_tag(values) != tag
                or tag <= previous_tags[profile] or tag in result):
            raise ValueError(f"{source} manifest coordinate/order mismatch")
        result[tag] = {"family": family, "local_index": index, "profile": profile, "source": source}
        locals_[profile] += 1
        previous_tags[profile] = tag
        previous_profile = profile
    return result


def terminal_coverage(receipt_path: Path, receipt_pin: str, inventory: Path,
                      inventory_pin: str, rows: list[dict]) -> tuple[dict, list[dict], list[Path]]:
    receipt = read_json(receipt_path, receipt_pin, "coverage receipt")
    if receipt.get("schema") != COVERAGE_SCHEMA or receipt.get("live_named_outputs_mutated") is not False:
        raise ValueError("coverage receipt is not a durable audit")
    receipt_fields = {"aws", "host_ledger_snapshot", "inputs", "live_campaign", "live_named_output_paths",
                      "live_named_outputs_mutated", "live_outputs_after", "live_outputs_before", "outputs",
                      "schema", "summary", "timestamp_utc"}
    summary, inputs, outputs = receipt.get("summary", {}), receipt.get("inputs", {}), receipt.get("outputs", {})
    input_fields = {"all_even_manifest", "all_even_manifest_sha256", "compact_inventory",
                    "compact_inventory_sha256", "complement_manifest", "complement_manifest_sha256",
                    "publisher", "publisher_sha256", "reconciler", "reconciler_sha256"}
    total = len(rows)
    summary_fields = {"anomalies", "certified", "cnf_sha_comparable_count", "cnf_sha_divergent_count",
                      "fleet_claim_tags", "fleet_in_flight", "fleet_ledger_rows",
                      "fleet_unknown_without_cert", "host_ledger_rows", "pending", "status_total",
                      "unknown_tags"}
    if (set(receipt) != receipt_fields or set(inputs) != input_fields or set(summary) != summary_fields
            or summary.get("certified") != total or summary.get("status_total") != total
            or summary.get("fleet_in_flight") != 0 or summary.get("pending") != 0
            or summary.get("anomalies") != {} or summary.get("cnf_sha_divergent_count") != 0
            or any(value != [] for value in summary.get("unknown_tags", {}).values())
            or receipt.get("live_outputs_before") != receipt.get("live_outputs_after")):
        raise ValueError("coverage is not exact terminal coverage")
    if (set(receipt.get("aws", {})) != {"bucket", "profile", "s3_prefix"}
            or any(not isinstance(value, str) or not value for value in receipt["aws"].values())
            or not STAMP.fullmatch(str(receipt.get("timestamp_utc", "")))):
        raise ValueError("coverage receipt provenance malformed")
    root = receipt_path.parent
    expected = {"counts.json", "coverage.tsv", "inventory_universe_diff.tsv"}
    host_snapshot = receipt.get("host_ledger_snapshot", {})
    live_paths = receipt.get("live_named_output_paths", {})
    live_before, live_after = receipt.get("live_outputs_before", {}), receipt.get("live_outputs_after", {})
    if (set(host_snapshot) != {"count", "identity_sha256"}
            or type(host_snapshot.get("count")) is not int or host_snapshot["count"] < 0
            or SHA.fullmatch(str(host_snapshot.get("identity_sha256", ""))) is None
            or set(live_paths) != expected or any(not isinstance(value, str) or not Path(value).is_absolute()
                                                   for value in live_paths.values())
            or set(live_before) != expected or set(live_after) != expected):
        raise ValueError("coverage nested provenance malformed")
    for identities in (live_before, live_after):
        if any(not isinstance(item, dict) or set(item) != {"bytes", "sha256"}
               or type(item["bytes"]) is not int or item["bytes"] < 0
               or SHA.fullmatch(str(item["sha256"])) is None for item in identities.values()):
            raise ValueError("coverage live output identity malformed")
    if set(outputs) != expected:
        raise ValueError("coverage output set mismatch")
    captured = [receipt_path]
    for path_key, pin_key in (("all_even_manifest", "all_even_manifest_sha256"),
            ("compact_inventory", "compact_inventory_sha256"),
            ("complement_manifest", "complement_manifest_sha256"), ("publisher", "publisher_sha256"),
            ("reconciler", "reconciler_sha256")):
        path = Path(inputs[path_key])
        require_file(path, inputs[pin_key], f"coverage {path_key}")
        captured.append(path)
    manifests = {
        "all_even_capacity": read_manifest(Path(inputs["all_even_manifest"]), "all_even_capacity"),
        "non_all_even_capacity": read_manifest(Path(inputs["complement_manifest"]), "non_all_even_capacity"),
    }
    if set(manifests["all_even_capacity"]) & set(manifests["non_all_even_capacity"]):
        raise ValueError("capacity manifests overlap")
    if set(manifests["all_even_capacity"]) | set(manifests["non_all_even_capacity"]) != {row["tag"] for row in rows}:
        raise ValueError("capacity manifest union mismatch")
    raw_universe = inventory_universe(Path(inputs["compact_inventory"]))
    filter_module = load_filter()
    retained = []
    for raw in Path(inputs["compact_inventory"]).read_text(encoding="ascii").splitlines():
        profile, *values = map(int, raw.split())
        if filter_module.has_cross_miss_capacity(tuple(values)):
            retained.append(raw + "\n")
    if inventory.read_bytes() != "".join(retained).encode("ascii"):
        raise ValueError("capacity inventory is not the exact pinned-filter output in raw order")
    if any(raw_universe.get(row["tag"]) != row["profile"] for row in rows):
        raise ValueError("capacity inventory is not a profile-preserving subset of raw inventory")
    for name in sorted(expected):
        item = outputs[name]
        if not isinstance(item, dict) or set(item) != {"bytes", "sha256"}:
            raise ValueError("coverage output identity malformed")
        path = root / name
        require_file(path, item["sha256"], f"coverage {name}")
        if path.stat().st_size != item["bytes"]:
            raise ValueError("coverage output byte mismatch")
        captured.append(path)
    counts = json.loads((root / "counts.json").read_text())
    count_fields = {"all_even_capacity", "anomalies", "capacity_inventory_total", "capacity_only_error",
        "certified_s3_tags", "cnf_sha_comparable_count", "cnf_sha_divergent_count",
        "cnf_sha_divergent_tags", "compact_inventory_total", "compact_only_pre_capacity",
        "fleet_claim_tags", "fleet_ledger_rows", "fleet_unknown_without_cert", "fleet_v2_claim_tags",
        "fleet_v2_ledger_rows", "fleet_v3_claim_tags", "fleet_v3_ledger_rows", "host_ledger_rows",
        "non_all_even_capacity", "status_counts", "status_total", "unknown_tags"}
    statuses = counts.get("status_counts", {})
    if (set(counts) != count_fields or counts.get("capacity_inventory_total") != total
            or counts.get("certified_s3_tags") != total
            or counts.get("status_total") != total
            or statuses != {"certified-in-S3": total, "fleet-in-flight": 0, "pending": 0}
            or counts.get("anomalies") != {} or counts.get("cnf_sha_divergent_count") != 0
            or counts.get("cnf_sha_divergent_tags") != []
            or any(value != [] for value in counts.get("unknown_tags", {}).values())):
        raise ValueError("coverage counts are not exact terminal coverage")
    if counts.get("compact_inventory_total") != len(raw_universe):
        raise ValueError("raw compact inventory count mismatch")
    if (counts.get("all_even_capacity") != len(manifests["all_even_capacity"])
            or counts.get("non_all_even_capacity") != len(manifests["non_all_even_capacity"])
            or counts.get("host_ledger_rows") != host_snapshot["count"]):
        raise ValueError("coverage manifest/host count mismatch")
    if tuple(sum(1 for row in rows if row["profile"] == profile) for profile in range(5)) == PROFILE_COUNTS:
        if counts.get("compact_inventory_total") != 13541 or counts.get("compact_only_pre_capacity") != 190 \
                or counts.get("capacity_only_error") != 0:
            raise ValueError("production capacity universe mismatch")
    with (root / "coverage.tsv").open(newline="") as stream:
        reader = csv.DictReader(stream, delimiter="\t")
        if tuple(reader.fieldnames or ()) != COVERAGE_HEADER:
            raise ValueError("coverage header mismatch")
        coverage = list(reader)
    by_tag = {row["tag"]: row for row in coverage}
    if len(by_tag) != len(coverage) or set(by_tag) != {row["tag"] for row in rows}:
        raise ValueError("coverage tag universe mismatch")
    ordered = []
    for item in rows:
        row = by_tag[item["tag"]]
        source = row["inventory_source"]
        manifest = manifests.get(source, {}).get(item["tag"])
        if (row["profile"] != str(item["profile"]) or row["family"] != PROFILE_NAMES[item["profile"]]
                or not row["local_index"].isdigit()
                or manifest is None or manifest["profile"] != item["profile"]
                or manifest["family"] != row["family"] or manifest["local_index"] != int(row["local_index"])
                or row["status"] != "certified-in-S3" or row["certified_s3"] != "1"
                or row["cnf_sha_divergent"] != "0"):
            raise ValueError(f"{item['tag']}: coverage coordinate/status mismatch")
        ordered.append(row)
    return receipt, ordered, captured


def ledger_path(root: Path, namespace: str, tag: str) -> Path:
    return root / tag / "ledger.line" if namespace == "host" else root / f"{tag}.line"


def parse_ledger(path: Path, namespace: str, tag: str, profile: int, source_local_index: int) -> tuple[dict, bytes]:
    safe_path(path, f"{namespace} ledger")
    raw = path.read_bytes()
    if raw.count(b"\n") != 1 or not raw.endswith(b"\n"):
        raise ValueError(f"{tag}: ledger must be exactly one newline-terminated line")
    try:
        tokens = raw[:-1].decode("ascii").split(" ")
    except UnicodeDecodeError as error:
        raise ValueError(f"{tag}: ledger is not ASCII") from error
    if any(not token for token in tokens) or len(tokens) < 5 or not STAMP.fullmatch(tokens[0]) \
            or tokens[1] != tag or tokens[2] != f"p={profile}" \
            or tokens[3] != f"i={source_local_index}" or tokens[4] != "UNSAT":
        raise ValueError(f"{tag}: ledger prefix malformed")
    pairs = [token.split("=", 1) for token in (*tokens[2:4], *tokens[5:])]
    if any(len(pair) != 2 for pair in pairs) or len({pair[0] for pair in pairs}) != len(pairs):
        raise ValueError(f"{tag}: duplicate or non-key ledger token")
    values = dict(pairs)
    expected = set(COMMON_KEYS) | ({"node"} if namespace != "host" else set())
    expected_order = list(COMMON_KEYS) + (["node"] if namespace != "host" else [])
    if set(values) != expected or [pair[0] for pair in pairs] != expected_order:
        raise ValueError(f"{tag}: ledger keys mismatch")
    if values["rc"] != "20" or values["trim"] != "VERIFIED" or values["compact"] != "ok" \
            or values["upload"] != "uploaded":
        raise ValueError(f"{tag}: ledger terminal markers mismatch")
    numeric = ("p", "i", "emit_s", "solve_s", "trim_s", "cap_s", "cnf_clauses",
               "drat_bytes", "raw_lrat_bytes", "compact_bytes")
    if any(not values[key].isdigit() for key in numeric):
        raise ValueError(f"{tag}: ledger numeric field malformed")
    if int(values["p"]) != profile or int(values["i"]) != source_local_index:
        raise ValueError(f"{tag}: ledger coordinate mismatch")
    for key in ("cnf_sha256", "raw_lrat_sha256", "compact_lrat_sha256", "compact_gz_sha256"):
        if SHA.fullmatch(values[key]) is None:
            raise ValueError(f"{tag}: ledger SHA malformed")
    if namespace != "host" and NODE.fullmatch(values["node"]) is None:
        raise ValueError(f"{tag}: fleet node malformed")
    identity = {key: int(values[key]) if key in {"p", "i", "cnf_clauses", "raw_lrat_bytes", "compact_bytes"}
                else values[key] for key in CERTIFICATE_KEYS}
    return identity, raw


def parse_unknown_ledger(path: Path, namespace: str, tag: str, profile: int,
                         source_local_index: int, cnf_sha256: str) -> bytes:
    safe_path(path, f"{namespace} ledger")
    raw = path.read_bytes()
    if raw.count(b"\n") != 1 or not raw.endswith(b"\n"):
        raise ValueError(f"{tag}: UNKNOWN ledger line malformed")
    tokens = raw[:-1].decode("ascii").split(" ")
    expected = [STAMP, tag, f"p={profile}", f"i={source_local_index}", "UNKNOWN", "rc=0",
                None, None, f"cnf_sha256={cnf_sha256}"]
    if (len(tokens) != len(expected) + (1 if namespace != "host" else 0)
            or not STAMP.fullmatch(tokens[0]) or tokens[1:6] != expected[1:6]
            or not re.fullmatch(r"solve_s=\d+", tokens[6])
            or not re.fullmatch(r"cap_s=\d+", tokens[7]) or tokens[8] != expected[8]
            or (namespace != "host" and (not tokens[9].startswith("node=")
                or NODE.fullmatch(tokens[9].removeprefix("node=")) is None))):
        raise ValueError(f"{tag}: UNKNOWN ledger line malformed")
    return raw


def source_presence(row: dict, namespace: str) -> tuple[bool, bool, str, str]:
    if namespace == "host":
        verdict, digest = row["host_verdict"], row["host_cnf_sha256"]
        present = bool(verdict or digest)
        if row["host_unsat"] != str(int(verdict == "UNSAT")):
            raise ValueError(f"{row['tag']}: host coverage flag mismatch")
    else:
        verdict, digest = row[f"fleet_{namespace}_verdict"], row[f"fleet_{namespace}_cnf_sha256"]
        present = bool(verdict or digest)
        if row[f"fleet_{namespace}_claim"] not in {"0", "1"}:
            raise ValueError(f"{row['tag']}: {namespace} claim flag malformed")
    if present and (verdict not in {"UNSAT", "UNKNOWN"} or SHA.fullmatch(digest) is None):
        raise ValueError(f"{row['tag']}: {namespace} coverage evidence mismatch")
    if not present and (verdict or digest):
        raise ValueError(f"{row['tag']}: partial {namespace} coverage evidence")
    return present, verdict == "UNSAT", verdict, digest


def validate_effective_fleet(row: dict, present: dict[str, bool]) -> None:
    if row["fleet_claim"] not in {"0", "1"}:
        raise ValueError(f"{row['tag']}: fleet claim flag malformed")
    expected_namespace = "v3" if present["v3"] else "v2" if present["v2"] else None
    verdict = row[f"fleet_{expected_namespace}_verdict"] if expected_namespace else ""
    digest = row[f"fleet_{expected_namespace}_cnf_sha256"] if expected_namespace else ""
    if row["fleet_verdict"] != verdict or row["fleet_cnf_sha256"] != digest:
        raise ValueError(f"{row['tag']}: effective fleet coverage mismatch")
    claimed = row["fleet_v2_claim"] == "1" or row["fleet_v3_claim"] == "1"
    if row["fleet_claim"] != str(int(claimed)):
        raise ValueError(f"{row['tag']}: fleet claim union mismatch")


def fsync_tree(root: Path) -> None:
    for path in sorted(root.rglob("*"), reverse=True):
        if path.is_file():
            with path.open("rb") as stream:
                os.fsync(stream.fileno())
        elif path.is_dir():
            fd = os.open(path, os.O_RDONLY)
            try: os.fsync(fd)
            finally: os.close(fd)
    fd = os.open(root, os.O_RDONLY)
    try: os.fsync(fd)
    finally: os.close(fd)


def snapshot(*, coverage_receipt: Path, coverage_receipt_sha256: str,
             capacity_inventory: Path, capacity_inventory_sha256: str,
             host_root: Path, v2_root: Path, v3_root: Path, output: Path,
             profile_counts: tuple[int, ...] = PROFILE_COUNTS,
             before_receipt=None) -> dict:
    producer = Path(__file__).resolve()
    helper = HERE / "filter_h1_capacity_inventory.py"
    require_file(capacity_inventory, capacity_inventory_sha256, "capacity inventory")
    for root, namespace in ((host_root, "host"), (v2_root, "v2"), (v3_root, "v3")):
        safe_path(root, f"{namespace} ledger root", kind="dir")
    safe_path(output, "output", absent=True)
    rows = inventory_rows(capacity_inventory, profile_counts)
    receipt, coverage, captured = terminal_coverage(coverage_receipt, coverage_receipt_sha256,
                                                    capacity_inventory, capacity_inventory_sha256, rows)
    captured.extend([producer, helper, capacity_inventory])
    roots = {"host": host_root, "v2": v2_root, "v3": v3_root}
    selected = []
    root_entries = {namespace: [] for namespace in roots}
    raw_selected = []
    for item, cover in zip(rows, coverage, strict=True):
        tag = item["tag"]
        parsed = {}
        presence = {}
        for namespace in ("host", "v2", "v3"):
            expected, terminal, verdict, digest = source_presence(cover, namespace)
            presence[namespace] = expected
            path = ledger_path(roots[namespace], namespace, tag)
            exists = path.exists() or path.is_symlink()
            if exists != expected:
                raise ValueError(f"{tag}: {namespace} canonical ledger presence mismatch")
            if not exists:
                continue
            root_entries[namespace].append({"path": str(path), "sha256": sha256(path)})
            if not terminal:
                parse_unknown_ledger(path, namespace, tag, item["profile"], int(cover["local_index"]), digest)
                captured.append(path)
                continue
            identity, raw = parse_ledger(path, namespace, tag, item["profile"], int(cover["local_index"]))
            if identity["cnf_sha256"] != digest:
                raise ValueError(f"{tag}: {namespace} coverage CNF mismatch")
            parsed[namespace] = (identity, raw, path)
            captured.append(path)
        validate_effective_fleet(cover, presence)
        if not parsed:
            raise ValueError(f"{tag}: no terminal ledger evidence")
        identities = [entry[0] for entry in parsed.values()]
        if any(identity != identities[0] for identity in identities[1:]):
            raise ValueError(f"{tag}: overlapping ledger identity conflict")
        chosen = next(namespace for namespace in ("v3", "v2", "host") if namespace in parsed)
        identity, raw, source = parsed[chosen]
        relative = f"ledgers/{chosen}/{tag}.line"
        sources = {}
        for namespace in ("host", "v2", "v3"):
            if namespace not in parsed:
                sources[namespace] = None
            else:
                ident, source_raw, source_path = parsed[namespace]
                sources[namespace] = {"namespace": namespace, "source_path": str(source_path),
                                      "sha256": hashlib.sha256(source_raw).hexdigest()}
        selected.append({"capacity_local_index": item["local_index"], "certificate_identity": identity,
                         "selected": {"namespace": chosen,
                         "path": relative, "sha256": hashlib.sha256(raw).hexdigest()},
                         "sources": sources, "tag": tag})
        raw_selected.append((relative, raw))
    discovered = {
        "host": {str(path) for path in host_root.glob("*/ledger.line")},
        "v2": {str(path) for path in v2_root.glob("*.line")},
        "v3": {str(path) for path in v3_root.glob("*.line")},
    }
    if any(discovered[namespace] != {entry["path"] for entry in root_entries[namespace]}
           for namespace in roots):
        raise ValueError("canonical ledger root/path set mismatch")
    count_keys = {"host": "host_ledger_rows", "v2": "fleet_v2_ledger_rows", "v3": "fleet_v3_ledger_rows"}
    counts_value = json.loads((coverage_receipt.parent / "counts.json").read_text())
    if any(len(root_entries[namespace]) != counts_value[count_keys[namespace]] for namespace in roots):
        raise ValueError("canonical ledger root count mismatch")
    pins = {str(path): sha256(path) for path in captured}
    staging = Path(tempfile.mkdtemp(prefix=".h1-ledger-snapshot-stage.", dir=output.parent))
    try:
        for relative, raw in raw_selected:
            destination = staging / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(raw)
        document = {"capacity_inventory_sha256": capacity_inventory_sha256,
                    "coverage_receipt_sha256": coverage_receipt_sha256,
                    "profile_counts": list(profile_counts), "rows": selected, "schema": SCHEMA}
        (staging / "selected-ledgers.json").write_bytes(canonical(document))
        roots_identity = {}
        for namespace, root in roots.items():
            entries = root_entries[namespace]
            roots_identity[namespace] = {"count": len(entries), "identity_sha256":
                hashlib.sha256(canonical(entries)).hexdigest(), "path": str(root)}
        snapshot_identity = hashlib.sha256(canonical([{"path": rel, "sha256": hashlib.sha256(raw).hexdigest(),
                                                       "bytes": len(raw)} for rel, raw in raw_selected])).hexdigest()
        result = {"capacity_inventory_path": str(capacity_inventory),
                  "capacity_inventory_sha256": capacity_inventory_sha256,
                  "coverage_receipt_path": str(coverage_receipt),
                  "coverage_receipt_sha256": coverage_receipt_sha256,
                  "leaf_count": len(rows), "ledger_roots": roots_identity,
                  "inventory_helper_path": str(helper), "inventory_helper_sha256": pins[str(helper)],
                  "producer_path": str(producer), "producer_sha256": pins[str(producer)],
                  "profile_counts": list(profile_counts), "schema": RECEIPT_SCHEMA,
                  "selected_ledger_identity_sha256": snapshot_identity,
                  "snapshot_path": "selected-ledgers.json",
                  "snapshot_sha256": sha256(staging / "selected-ledgers.json")}
        if before_receipt is not None:
            before_receipt()
        for path, pin in pins.items():
            try:
                require_file(Path(path), pin, "captured input")
            except ValueError as error:
                raise ValueError("input drift before receipt") from error
        for root, namespace in ((host_root, "host"), (v2_root, "v2"), (v3_root, "v3")):
            safe_path(root, f"{namespace} ledger root", kind="dir")
        safe_path(output.parent, "output parent", kind="dir")
        for relative, raw in raw_selected:
            if (staging / relative).read_bytes() != raw:
                raise ValueError("staged ledger drift before receipt")
        (staging / "receipt.json").write_bytes(canonical(result))
        fsync_tree(staging)
        if output.exists() or output.is_symlink():
            raise ValueError("output appeared before publication")
        staging.rename(output)
        parent_fd = os.open(output.parent, os.O_RDONLY)
        try: os.fsync(parent_fd)
        finally: os.close(parent_fd)
        return result
    except Exception:
        if staging.exists():
            shutil.rmtree(staging)
        raise


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--coverage-receipt", type=Path, required=True)
    parser.add_argument("--coverage-receipt-sha256", required=True)
    parser.add_argument("--capacity-inventory", type=Path, required=True)
    parser.add_argument("--capacity-inventory-sha256", required=True)
    parser.add_argument("--host-root", type=Path, required=True)
    parser.add_argument("--v2-root", type=Path, required=True)
    parser.add_argument("--v3-root", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    snapshot(**vars(args))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
