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
    "certificate_key_present", "certificate_ledger_valid", "certificate_key_conflict",
    "certified_s3", "host_unsat", "host_cnf_sha256", "host_verdict",
    "fleet_claim", "fleet_cnf_sha256", "fleet_verdict", "cnf_sha_divergent",
    "fleet_v2_claim", "fleet_v2_cnf_sha256", "fleet_v2_verdict",
    "fleet_v3_claim", "fleet_v3_cnf_sha256", "fleet_v3_verdict",
)


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


def reconcile(inventory: list[InventoryRow], host: dict[str, LedgerRow],
              v2_rows: dict[str, LedgerRow], v3_rows: dict[str, LedgerRow],
              key_present: set[str], v2_claims: set[str], v3_claims: set[str]):
    by_tag = {row.tag: row for row in inventory}
    if len(inventory) != len(by_tag):
        fail("capacity census contains duplicate tags")
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
        conflict = present and not ledger_valid
        certified = present and ledger_valid
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
            int(present), int(ledger_valid), int(conflict), int(certified), int(host_unsat),
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
    rows, summary, divergent = reconcile(inventory, host, v2_rows, v3_rows, keys, v2_claims, v3_claims)
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
