#!/usr/bin/env python3
"""Refresh H1 coverage while separating S3 key presence from ledger validity.

This is the tracked successor to the campaign-local ``reconcile_coverage.py``.
An object name is availability evidence, not proof validity.  In particular, a
failed producer must not become "certified" merely because it uploaded an empty
or otherwise unverified gzip object.  Even ``certificate_ledger_valid`` remains
provisional until the terminal full-object readback binds the object bytes.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import re
from collections import Counter
from dataclasses import dataclass
from pathlib import Path


TAG_RE = re.compile(r"[0-9a-f]{16}")
SHA_RE = re.compile(r"[0-9a-f]{64}")
EMPTY_SHA256 = hashlib.sha256(b"").hexdigest()
TABLE_PAIRS = tuple(
    (c, j) for c in range(8) for j in range(c + 1, 8) if j != (c ^ 1)
)
COVERAGE_COLUMNS = (
    "tag", "profile", "family", "local_index", "inventory_source", "status",
    "certificate_key_present", "certificate_ledger_valid", "certificate_readback_valid",
    "certificate_key_conflict", "certified_s3", "host_unsat", "host_cnf_sha256", "host_verdict",
    "fleet_claim", "fleet_cnf_sha256", "fleet_verdict", "cnf_sha_divergent",
    "fleet_v2_claim", "fleet_v2_cnf_sha256", "fleet_v2_verdict",
    "fleet_v3_claim", "fleet_v3_cnf_sha256", "fleet_v3_verdict",
)
CONFLICT_AUDIT_SCHEMA = "erdos85-h1-conflict-readback-audit-v1"
CONFLICT_EXECUTOR_SHA256 = "98cacdb8c00dd0c99b4fb3116496b37e7628a5425673243f02ae6ddbaeabacb8"
CONFLICT_HELPER_SHA256 = {
    "capacity-filter": "a0f75f34d74cb8e3d48310b8f2e7b9544bba690110c0256c03f1b78bc9745e81",
    "queue-format": "5acf5ba65a4d3ea3f1f2aa603b102aa762ebbf91b1b2365645cb0af9060e7636",
}
CONFLICT_INPUT_SHA256 = {
    "audit-receipt": "d03a41d327b8a059b6a516a254789814a2f608d3024114b82701fa2683ba1995",
    "capacity-inventory": "81d515472be48a43806f9c1c7343b4b715c98fe5a02a82e2b76244c1b015fd1b",
    "queue": "b7eba5dabf8a860c5af7015032203f38608ca9750182da06a2bbf0fe12d77380",
    "queue-receipt": "88665dcb8a2bb25890dd6d14fc17df4b7ad39b9d449690ae6dd8ff0600ffc86a",
}
CONFLICT_IMAGE = "lean4-arm64@sha256:a5ca6c4e3328a1832d5f9b814ab7c1e35616903b3956341962a5b1a96fb6dff6"
CONFLICT_CACHE_VOLUME = "lean-mathlib-cache"
CONFLICT_LRATREPLAY_SHA256 = "37aad1d5c64a75fcb68e1ea587b2080b06c157a19c883b01d145b28b891c428c"
CONFLICT_V2CNF_SHA256 = "4bd9604c6d670ad65a8ca332a26dbf35132418634a3b0678c177c8b2cfff4bf6"
EXPECTED_CONFLICT_JOBS = {
    tag: {"certificate_key": f"sat49/campaign-20260825/h1/{tag}.compact.lrat.gz",
          "family": "BBBB", "local_index": local_index, "profile": 0, "tag": tag}
    for tag, local_index in (("dba11866daee2215", 1285), ("df21cf066affa6f4", 1304),
                             ("e7c1dfc9654d954c", 1338))
}
EXPECTED_CONFLICT_TAGS = set(EXPECTED_CONFLICT_JOBS)


@dataclass(frozen=True)
class InventoryRow:
    tag: str
    profile: int
    family: str
    local_index: int
    source: str


@dataclass(frozen=True)
class LedgerRow:
    tag: str
    verdict: str
    attributes: dict[str, str]
    raw: str

    @property
    def rc(self) -> str:
        return self.attributes.get("rc", "")

    @property
    def cnf_sha256(self) -> str:
        return self.attributes.get("cnf_sha256", "")

    def is_verified_uploaded_unsat(self) -> bool:
        """Producer evidence only; terminal object readback is still required."""
        try:
            raw_bytes = int(self.attributes.get("raw_lrat_bytes", ""))
            compact_bytes = int(self.attributes.get("compact_bytes", ""))
        except ValueError:
            return False
        raw_sha = self.attributes.get("raw_lrat_sha256", "")
        compact_sha = self.attributes.get("compact_lrat_sha256", "")
        gzip_sha = self.attributes.get("compact_gz_sha256", "")
        return (
            self.verdict == "UNSAT"
            and self.rc == "20"
            and self.attributes.get("trim") == "VERIFIED"
            and self.attributes.get("compact") == "ok"
            and self.attributes.get("upload") == "uploaded"
            and raw_bytes > 0
            and compact_bytes > 0
            and all(SHA_RE.fullmatch(value or "") for value in (raw_sha, compact_sha, gzip_sha))
            and raw_sha != EMPTY_SHA256
            and compact_sha != EMPTY_SHA256
        )


def fail(message: str) -> "NoReturn":
    raise RuntimeError(message)


def parse_ledger(raw: str, origin: str) -> LedgerRow:
    fields = raw.strip().split()
    if len(fields) < 4 or not TAG_RE.fullmatch(fields[1]):
        fail(f"{origin}: malformed ledger row: {raw[:160]!r}")
    pairs = [field.split("=", 1) for field in fields if "=" in field]
    if len({key for key, _ in pairs}) != len(pairs):
        fail(f"{origin}: duplicate ledger attribute")
    attributes = dict(pairs)
    verdict = next((field for field in fields[2:] if "=" not in field), "")
    if not verdict:
        fail(f"{origin}: ledger row has no verdict token")
    sha = attributes.get("cnf_sha256", "")
    if sha and not SHA_RE.fullmatch(sha):
        fail(f"{origin}: malformed cnf_sha256={sha!r}")
    return LedgerRow(fields[1], verdict, attributes, raw.strip())


def read_manifest(path: Path, source: str) -> list[InventoryRow]:
    rows = []
    for line_number, raw in enumerate(path.read_text().splitlines(), 1):
        fields = raw.split("\t")
        if len(fields) < 4 or not TAG_RE.fullmatch(fields[0]):
            fail(f"{path}:{line_number}: malformed inventory row")
        rows.append(InventoryRow(fields[0], int(fields[1]), fields[2], int(fields[3]), source))
    return rows


def read_host_ledgers(root: Path) -> dict[str, LedgerRow]:
    result = {}
    for path in root.glob("*/ledger.line"):
        row = parse_ledger(path.read_text(), str(path))
        if row.tag != path.parent.name:
            fail(f"{path}: tag disagrees with parent directory")
        result[row.tag] = row
    return result


def read_fleet_ledgers(cache: Path) -> dict[str, LedgerRow]:
    result = {}
    for path in cache.glob("*.line"):
        row = parse_ledger(path.read_text(), str(path))
        if row.tag != path.stem:
            fail(f"{path}: tag disagrees with filename")
        result[row.tag] = row
    return result


def iter_s3_objects(client: object, bucket: str, prefix: str):
    paginator = client.get_paginator("list_objects_v2")
    for page in paginator.paginate(Bucket=bucket, Prefix=prefix):
        yield from page.get("Contents", ())


def sync_fleet_ledgers(client: object, bucket: str, prefix: str,
                       namespace: str, cache: Path) -> None:
    cache.mkdir(parents=True, exist_ok=True)
    ledger_prefix = f"{prefix}/{namespace}/ledger/"
    seen = set()
    for item in iter_s3_objects(client, bucket, ledger_prefix):
        key = item["Key"]
        if not key.startswith(ledger_prefix):
            fail(f"S3 returned key outside requested ledger prefix: {key!r}")
        name = key[len(ledger_prefix):]
        if "/" in name:
            fail(f"nested ledger key is not canonical: {key!r}")
        if not name.endswith(".line"):
            continue
        tag = name[:-len(".line")]
        if not TAG_RE.fullmatch(tag) or key != f"{ledger_prefix}{tag}.line":
            fail(f"malformed ledger key is not canonical: {key!r}")
        if tag in seen:
            fail(f"duplicate ledger key for tag {tag}: {key!r}")
        seen.add(tag)
        destination = cache / name
        if not destination.exists() or destination.stat().st_size != item["Size"]:
            client.download_file(bucket, key, str(destination))


def list_s3_tags(client: object, bucket: str, prefix: str, suffix: str) -> set[str]:
    result = set()
    for item in iter_s3_objects(client, bucket, prefix):
        key = item["Key"]
        if not key.startswith(prefix):
            fail(f"S3 returned key outside requested prefix: {key!r}")
        name = key[len(prefix):]
        if "/" in name:
            fail(f"nested object key is not canonical: {key!r}")
        if suffix and not name.endswith(suffix):
            continue
        tag = name[:-len(suffix)] if suffix else name
        if not TAG_RE.fullmatch(tag) or key != f"{prefix}{tag}{suffix}":
            fail(f"malformed object key is not canonical: {key!r}")
        if tag in result:
            fail(f"duplicate object key for tag {tag}: {key!r}")
        result.add(tag)
    return result


def worker_tag(values: tuple[int, ...]) -> str:
    table = {pair: value for pair, value in zip(TABLE_PAIRS, values, strict=True) if value}
    return hashlib.sha1(json.dumps(sorted(table.items())).encode()).hexdigest()[:16]


def read_compact_inventory(path: Path) -> dict[str, tuple[int, tuple[int, ...]]]:
    result = {}
    for line_number, raw in enumerate(path.read_text().splitlines(), 1):
        values = tuple(map(int, raw.split()))
        if len(values) != 25:
            fail(f"{path}:{line_number}: expected profile plus 24 table values")
        tag = worker_tag(values[1:])
        if tag in result:
            fail(f"{path}:{line_number}: duplicate tag {tag}")
        result[tag] = (values[0], values[1:])
    return result


def atomic_tsv(path: Path, header: tuple[str, ...] | list[str], rows: list[list[object]]) -> None:
    temporary = path.with_suffix(path.suffix + ".tmp")
    with temporary.open("w", newline="") as stream:
        writer = csv.writer(stream, delimiter="\t", lineterminator="\n")
        writer.writerow(header)
        writer.writerows(rows)
    temporary.replace(path)


def read_conflict_audit(path: Path, expected_sha256: str, bucket: str,
                        s3_prefix: str) -> tuple[set[str], str]:
    is_sha256 = lambda item: isinstance(item, str) and SHA_RE.fullmatch(item) is not None
    if not SHA_RE.fullmatch(expected_sha256):
        fail("conflict audit expected SHA-256 is malformed")
    raw = path.read_bytes()
    actual_sha256 = hashlib.sha256(raw).hexdigest()
    if actual_sha256 != expected_sha256:
        fail("conflict audit SHA-256 mismatch")
    try:
        value = json.loads(raw)
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        fail(f"conflict audit is malformed JSON: {error}")
    canonical = (json.dumps(value, ensure_ascii=True, allow_nan=False, sort_keys=True,
                            separators=(",", ":")) + "\n").encode("ascii")
    required = {"aws", "aws_auth", "cache_volume", "executor_sha256", "helper_sha256",
                "image", "input_paths", "inputs", "lratreplay_sha256", "results", "schema",
                "summary", "tool_versions", "v2cnf_sha256"}
    if (not isinstance(value, dict) or raw != canonical or set(value) != required
            or value.get("schema") != CONFLICT_AUDIT_SCHEMA
            or value.get("aws") != {"bucket": bucket, "profile": "2am-admin",
                                    "s3_prefix": s3_prefix}
            or value.get("aws_auth") != {"mode": "instance-role", "region": "us-east-1"}
            or value.get("executor_sha256") != CONFLICT_EXECUTOR_SHA256
            or value.get("helper_sha256") != CONFLICT_HELPER_SHA256
            or value.get("image") != CONFLICT_IMAGE
            or value.get("cache_volume") != CONFLICT_CACHE_VOLUME
            or value.get("lratreplay_sha256") != CONFLICT_LRATREPLAY_SHA256
            or value.get("v2cnf_sha256") != CONFLICT_V2CNF_SHA256
            or not isinstance(value.get("inputs"), dict)
            or any(value["inputs"].get(name) != digest
                   for name, digest in CONFLICT_INPUT_SHA256.items())
            or set(value["inputs"]) != {*CONFLICT_INPUT_SHA256, "aws", "docker"}
            or any(not is_sha256(value["inputs"].get(name))
                   for name in ("aws", "docker"))
            or not isinstance(value.get("results"), list)):
        fail("conflict audit exact provenance contract mismatch")
    classifications = ("canonical-valid", "canonical-invalid", "canonical-missing")
    counts = {name: 0 for name in classifications}
    seen, valid = set(), set()

    def job_sha256(job: dict) -> str:
        return hashlib.sha256((json.dumps(job, ensure_ascii=True, allow_nan=False,
                                          sort_keys=True, separators=(",", ":")) + "\n").encode(
                                              "ascii")).hexdigest()

    def valid_object(item: object, job: dict) -> bool:
        return (isinstance(item, dict)
                and set(item) == {"etag", "key", "last_modified", "sha256", "size", "version_id"}
                and item["key"] == job["certificate_key"]
                and isinstance(item["etag"], str) and bool(item["etag"])
                and isinstance(item["last_modified"], str) and bool(item["last_modified"])
                and is_sha256(item["sha256"])
                and type(item["size"]) is int and item["size"] > 0
                and (item["version_id"] is None
                     or isinstance(item["version_id"], str) and bool(item["version_id"])))

    def valid_validation(item: object, accepted: bool, replay_rc: tuple[int, ...]) -> bool:
        if not isinstance(item, dict) or set(item) != {
                "cnf_bytes", "cnf_clauses", "cnf_sha256", "replay_accepted", "replay_rc",
                "replay_stderr_sha256", "replay_stdout_sha256", "table_sha256", "v2cnf_check"}:
            return False
        marker = re.fullmatch(r"MATCH \(([0-9]+) clauses, top ([0-9]+)\)",
                              str(item["v2cnf_check"]))
        return (type(item["cnf_bytes"]) is int and item["cnf_bytes"] > 0
                and type(item["cnf_clauses"]) is int and item["cnf_clauses"] > 0
                and marker is not None and int(marker.group(1)) == item["cnf_clauses"]
                and item["replay_accepted"] is accepted
                and type(item["replay_rc"]) is int and item["replay_rc"] in replay_rc
                and all(is_sha256(item[name]) for name in
                        ("cnf_sha256", "replay_stderr_sha256", "replay_stdout_sha256",
                         "table_sha256")))

    base_keys = {"classification", "compact_bytes", "compact_lrat_sha256", "job",
                 "job_sha256", "object", "validation"}
    for result in value["results"]:
        job = result.get("job") if isinstance(result, dict) else None
        if (not isinstance(job, dict)
                or set(job) != {"certificate_key", "family", "local_index", "profile", "tag"}
                or not TAG_RE.fullmatch(str(job.get("tag", "")))
                or job != EXPECTED_CONFLICT_JOBS.get(job["tag"])
                or job["tag"] in seen or result.get("classification") not in classifications):
            fail("conflict audit result identity/classification mismatch")
        seen.add(job["tag"])
        classification = result["classification"]
        counts[classification] += 1
        if classification == "canonical-missing":
            if (set(result) != {"classification", "job", "job_sha256", "reason"}
                    or result["job_sha256"] != job_sha256(job)
                    or result["reason"] != "confirmed-not-found"):
                fail("conflict audit missing-result evidence mismatch")
            continue
        common = (result.get("job_sha256") == job_sha256(job)
                  and type(result.get("compact_bytes")) is int and result["compact_bytes"] > 0
                  and is_sha256(result.get("compact_lrat_sha256"))
                  and valid_object(result.get("object"), job))
        if classification == "canonical-valid":
            if (set(result) != base_keys or not common
                    or not valid_validation(result.get("validation"), True, (0,))):
                fail("conflict audit valid-result evidence mismatch")
            valid.add(job["tag"])
        elif result.get("failure_stage") == "gzip-or-compact-syntax":
            if (set(result) != {"classification", "failure_stage", "job", "job_sha256",
                               "object", "reason"}
                    or result["job_sha256"] != job_sha256(job)
                    or not valid_object(result.get("object"), job)
                    or not isinstance(result.get("reason"), str) or not result["reason"]):
                fail("conflict audit syntax-invalid evidence mismatch")
        elif result.get("failure_stage") == "semantic-replay":
            if (set(result) != base_keys | {"failure_stage", "reason"} or not common
                    or result.get("reason") != "LRAT rejected"
                    or not valid_validation(result.get("validation"), False, (0, 1))):
                fail("conflict audit replay-invalid evidence mismatch")
        else:
            fail("conflict audit invalid-result stage mismatch")
    if seen != EXPECTED_CONFLICT_TAGS:
        fail("conflict audit does not exactly cover the authoritative conflict queue")
    if value.get("summary") != counts:
        fail("conflict audit summary differs from results")
    return valid, actual_sha256


def reconcile(inventory: list[InventoryRow], host: dict[str, LedgerRow],
              v2_rows: dict[str, LedgerRow], v3_rows: dict[str, LedgerRow],
              key_present: set[str], v2_claims: set[str], v3_claims: set[str],
              readback_valid: set[str] | frozenset[str] = frozenset()):
    by_tag = {row.tag: row for row in inventory}
    if len(inventory) != len(by_tag):
        fail("capacity census contains duplicate tags")
    if not readback_valid <= set(by_tag):
        fail("conflict audit contains tag outside capacity inventory")
    claims = v2_claims | v3_claims
    counts: Counter[str] = Counter()
    anomalies: Counter[str] = Counter()
    divergent = []
    comparable = 0
    unknown_without_cert = 0
    manifest_rows = []
    conflicts = []
    for tag in sorted(by_tag):
        item, h, v2, v3 = by_tag[tag], host.get(tag), v2_rows.get(tag), v3_rows.get(tag)
        effective = v3 or v2
        shas = [row.cnf_sha256 if row else "" for row in (h, v2, v3)]
        diverges = len({value for value in shas if value}) > 1
        comparable += int(sum(bool(value) for value in shas) >= 2)
        if diverges:
            divergent.append(tag)
        present = tag in key_present
        ledger_valid = any(row and row.is_verified_uploaded_unsat() for row in (h, v2, v3))
        readback = tag in readback_valid
        conflict = present and not (ledger_valid or readback)
        certified = present and (ledger_valid or readback)
        if conflict:
            conflicts.append(tag)
            anomalies["certificate-key-present-without-valid-upload-ledger"] += 1
        host_unsat = bool(h and h.verdict == "UNSAT" and h.rc == "20")
        in_flight = ((tag in v2_claims and tag not in v2_rows)
                     or (tag in v3_claims and tag not in v3_rows)) and not present
        if conflict:
            status = "certificate-key-conflict"
        elif certified:
            status = "certified-in-S3"
        elif host_unsat:
            status = "host-ledgered-UNSAT-not-uploaded"
        elif in_flight:
            status = "fleet-in-flight"
        else:
            status = "pending"
        counts[status] += 1
        for namespace, row in (("v2", v2), ("v3", v3)):
            if row and row.is_verified_uploaded_unsat() and not present:
                anomalies[f"fleet-{namespace}-verified-upload-ledger-without-S3-key"] += 1
        if effective and effective.verdict == "UNKNOWN" and not present:
            unknown_without_cert += 1
        manifest_rows.append([
            tag, item.profile, item.family, item.local_index, item.source, status,
            int(present), int(ledger_valid), int(readback), int(conflict), int(certified), int(host_unsat),
            h.cnf_sha256 if h else "", h.verdict if h else "", int(tag in claims),
            effective.cnf_sha256 if effective else "", effective.verdict if effective else "",
            int(diverges), int(tag in v2_claims), v2.cnf_sha256 if v2 else "",
            v2.verdict if v2 else "", int(tag in v3_claims), v3.cnf_sha256 if v3 else "",
            v3.verdict if v3 else "",
        ])
    summary = {
        "anomalies": dict(sorted(anomalies.items())),
        "capacity_inventory_total": len(by_tag),
        "certificate_key_conflict_tags": conflicts,
        "certificate_key_conflict_count": len(conflicts),
        "certificate_key_present_tags": len(key_present & set(by_tag)),
        "certificate_ledger_valid_tags": sum(
            any(row and row.is_verified_uploaded_unsat() for row in
                (host.get(tag), v2_rows.get(tag), v3_rows.get(tag))) for tag in by_tag),
        "certificate_readback_valid_tags": len(readback_valid),
        "certificate_ledger_valid_present_tags": sum(
            tag in key_present and any(row and row.is_verified_uploaded_unsat() for row in
                (host.get(tag), v2_rows.get(tag), v3_rows.get(tag))) for tag in by_tag),
        "certificate_readback_valid_present_tags": len(readback_valid & key_present),
        "certificate_ledger_readback_valid_present_overlap_tags": sum(
            tag in key_present and tag in readback_valid
            and any(row and row.is_verified_uploaded_unsat() for row in
                    (host.get(tag), v2_rows.get(tag), v3_rows.get(tag))) for tag in by_tag),
        "certified_s3_tags": counts["certified-in-S3"],
        "cnf_sha_comparable_count": comparable,
        "cnf_sha_divergent_count": len(divergent),
        "cnf_sha_divergent_tags": divergent,
        "fleet_claim_tags": len(claims & set(by_tag)),
        "fleet_ledger_rows": len((set(v2_rows) | set(v3_rows)) & set(by_tag)),
        "fleet_unknown_without_cert": unknown_without_cert,
        "host_ledger_rows": len(set(host) & set(by_tag)),
        "status_counts": {key: counts[key] for key in (
            "certificate-key-conflict", "certified-in-S3", "fleet-in-flight", "pending",
            "host-ledgered-UNSAT-not-uploaded")},
        "status_total": sum(counts.values()),
    }
    return manifest_rows, summary, divergent


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--campaign", type=Path, required=True)
    parser.add_argument("--aws-profile", default="2am-admin")
    parser.add_argument("--bucket", default="2am-erdos85-certs")
    parser.add_argument("--s3-prefix", default="sat49/campaign-20260825")
    parser.add_argument("--compact-inventory", type=Path, required=True)
    parser.add_argument("--conflict-audit", type=Path)
    parser.add_argument("--conflict-audit-sha256")
    args = parser.parse_args()
    import boto3

    grind, output = args.campaign / "h1grind", args.campaign / "h1fleet/coverage"
    output.mkdir(parents=True, exist_ok=True)
    inventory = read_manifest(grind / "all_even_manifest.tsv", "all_even_capacity") + read_manifest(
        grind / "complement_manifest.tsv", "non_all_even_capacity")
    if len(inventory) != 13_351:
        fail(f"capacity census must contain 13,351 rows, got {len(inventory)}")
    client = boto3.Session(profile_name=args.aws_profile).client("s3")
    v2_cache, v3_cache = output / "fleet-ledger-cache", output / "fleet-v3-ledger-cache"
    sync_fleet_ledgers(client, args.bucket, args.s3_prefix, "h1-fleet-v2", v2_cache)
    sync_fleet_ledgers(client, args.bucket, args.s3_prefix, "h1-fleet-v3", v3_cache)
    host, v2_rows, v3_rows = read_host_ledgers(grind / "orbits"), read_fleet_ledgers(v2_cache), read_fleet_ledgers(v3_cache)
    keys = list_s3_tags(client, args.bucket, f"{args.s3_prefix}/h1/", ".compact.lrat.gz")
    v2_claims = list_s3_tags(client, args.bucket, f"{args.s3_prefix}/h1-fleet-v2/claims/", "")
    v3_claims = list_s3_tags(client, args.bucket, f"{args.s3_prefix}/h1-fleet-v3/claims/", "")
    if (args.conflict_audit is None) != (args.conflict_audit_sha256 is None):
        fail("conflict audit path and SHA-256 must be supplied together")
    readback_valid, conflict_audit_sha256 = (set(), "")
    if args.conflict_audit is not None:
        readback_valid, conflict_audit_sha256 = read_conflict_audit(
            args.conflict_audit, args.conflict_audit_sha256, args.bucket, args.s3_prefix)
    rows, summary, divergent = reconcile(
        inventory, host, v2_rows, v3_rows, keys, v2_claims, v3_claims, readback_valid)
    compact, tags = read_compact_inventory(args.compact_inventory), {row.tag for row in inventory}
    universe = []
    for tag in sorted(set(compact) | tags):
        relation = "both" if tag in compact and tag in tags else ("compact-only-pre-capacity" if tag in compact else "capacity-only-ERROR")
        universe.append([tag, relation, compact[tag][0] if tag in compact else "",
                         next((row.source for row in inventory if row.tag == tag), "")])
    summary.update({
        "all_even_capacity": sum(row.source == "all_even_capacity" for row in inventory),
        "non_all_even_capacity": sum(row.source == "non_all_even_capacity" for row in inventory),
        "fleet_v2_claim_tags": len(v2_claims & tags), "fleet_v2_ledger_rows": len(set(v2_rows) & tags),
        "fleet_v3_claim_tags": len(v3_claims & tags), "fleet_v3_ledger_rows": len(set(v3_rows) & tags),
        "unknown_tags": {"certified_s3": sorted(keys-tags), "fleet_v2_claim": sorted(v2_claims-tags),
            "fleet_v2_ledger": sorted(set(v2_rows)-tags), "fleet_v3_claim": sorted(v3_claims-tags),
            "fleet_v3_ledger": sorted(set(v3_rows)-tags), "host_ledger": sorted(set(host)-tags)},
        "compact_inventory_total": len(compact), "compact_only_pre_capacity": len(set(compact)-tags),
        "capacity_only_error": len(tags-set(compact)),
        "conflict_audit_sha256": conflict_audit_sha256,
    })
    atomic_tsv(output / "coverage.tsv", COVERAGE_COLUMNS, rows)
    atomic_tsv(output / "inventory_universe_diff.tsv",
               ["tag", "relation", "compact_profile", "capacity_source"], universe)
    temporary = output / "counts.json.tmp"
    temporary.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    temporary.replace(output / "counts.json")
    print(json.dumps(summary, indent=2, sort_keys=True))
    hard_errors = (bool(divergent) or any(summary["unknown_tags"].values())
                   or summary["capacity_only_error"] != 0 or summary["status_total"] != 13_351)
    return 1 if hard_errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
