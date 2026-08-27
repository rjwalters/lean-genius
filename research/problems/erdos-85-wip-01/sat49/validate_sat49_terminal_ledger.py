#!/usr/bin/env python3
"""Validate one transactional SAT49 terminal receipt.

The worker may write diagnostic/failure markers in other files, but a
``ledger.line`` is terminal state.  Consequently this parser accepts only a
fully certified UNSAT result or an independently reproduced and verified SAT
model.  It deliberately rejects legacy UNKNOWN, deferred, and partial rows.
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import re
from datetime import datetime
from pathlib import Path


SCHEMA = "erdos85-sat49-terminal-v1"
SHA256_RE = re.compile(r"[0-9a-f]{64}")
JOB_RE = re.compile(
    r"(?:h3_(?:b1|c1|c2|dist2)|h5_t[012])\."
    r"(?:cover-(?:left|right)|cube-[0-7]-[0-7])"
    r"(?:\.nested\.(?:cover-(?:left|right)|cube-[0-7]-[0-7]))?"
    r"(?:\.third\.(?:cover-(?:left|right)|cube-[0-7]-[0-7]))?"
)

COMMON = {
    "schema", "provenance", "mode", "rc", "solve_s", "solve_peak_rss_kb", "cap_s",
    "generator_kind", "generator_sha256", "manifest_sha256",
    "emitted_cnf_sha256", "solved_cnf_sha256", "cnf_bytes", "maxvar",
    "kissat_sha256",
}
UNSAT = {
    "raw_lrat_sha256", "raw_lrat_bytes", "trim", "trim_s",
    "trim_peak_rss_kb", "drat_trim_sha256", "compact_lrat_sha256",
    "compact_lrat_bytes", "compact_s", "compact_peak_rss_kb",
    "compactor_sha256", "lrat_kind", "native_lratcheck",
    "native_lratcheck_s", "native_lratcheck_peak_rss_kb",
    "lrat_check_sha256", "lean_lratreplay", "lean_lratreplay_s",
    "lean_lratreplay_peak_rss_kb", "lratreplay_sha256", "lean_image_digest",
    "compact_lrat_gz_sha256", "compact_lrat_gz_bytes", "upload",
    "remote_sha256",
}
SAT = {"reproduce_rc", "model", "model_verifier_sha256"}
HASH_FIELDS = {
    key for key in COMMON | UNSAT | SAT
    if key.endswith("_sha256") or key == "remote_sha256"
}
NONNEGATIVE_INTEGER_FIELDS = {
    "rc", "solve_s", "solve_peak_rss_kb", "cap_s", "cnf_bytes", "maxvar",
    "raw_lrat_bytes", "trim_s", "trim_peak_rss_kb", "compact_lrat_bytes",
    "compact_s", "compact_peak_rss_kb", "native_lratcheck_s",
    "native_lratcheck_peak_rss_kb", "lean_lratreplay_s",
    "lean_lratreplay_peak_rss_kb", "compact_lrat_gz_bytes", "reproduce_rc",
}


class ReceiptError(ValueError):
    pass


def manifest_identity(path: Path, expected_sha256: str | None = None
                      ) -> tuple[set[str], str]:
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    if expected_sha256 is not None:
        if SHA256_RE.fullmatch(expected_sha256) is None:
            raise ReceiptError("invalid expected manifest SHA256")
        if digest != expected_sha256:
            raise ReceiptError("supplied job manifest differs from its preflight pin")
    try:
        manifest = json.loads(path.read_text())
    except (json.JSONDecodeError, UnicodeDecodeError) as error:
        raise ReceiptError(f"invalid manifest JSON: {path}") from error
    schema = manifest.get("schema")
    if schema == "erdos85-small-high-cube-jobs-v1":
        groups = manifest.get("cells")
    elif schema in {"erdos85-small-high-nested-cube-jobs-v1",
                    "erdos85-small-high-third-cube-jobs-v1"}:
        groups = manifest.get("leaves")
    else:
        raise ReceiptError(f"unsupported job manifest schema: {schema}")
    if not isinstance(groups, dict) or not groups:
        raise ReceiptError("job manifest has no nonempty cell/leaf mapping")
    job_ids = []
    for group in groups.values():
        if not isinstance(group, dict) or not isinstance(group.get("jobs"), list):
            raise ReceiptError("job manifest group has no job list")
        for job in group["jobs"]:
            if not isinstance(job, dict) or not isinstance(job.get("id"), str):
                raise ReceiptError("job manifest contains a malformed job record")
            job_ids.append(job["id"])
    if len(set(job_ids)) != len(job_ids):
        raise ReceiptError("job manifest contains duplicate job ids")
    if not job_ids:
        raise ReceiptError("job manifest contains no jobs")
    return set(job_ids), digest


def file_identity(path: Path) -> tuple[str, int]:
    digest = hashlib.sha256()
    size = 0
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            digest.update(chunk)
            size += len(chunk)
    return digest.hexdigest(), size


def validate_artifacts(receipt: dict[str, str], solved_cnf: Path,
                       raw_lrat: Path | None = None,
                       compact_lrat: Path | None = None,
                       compact_lrat_gz: Path | None = None) -> None:
    cnf_sha, cnf_bytes = file_identity(solved_cnf)
    if (cnf_sha != receipt["solved_cnf_sha256"] or
            cnf_bytes != int(receipt["cnf_bytes"])):
        raise ReceiptError("solved CNF artifact identity mismatch")
    proof_paths = (raw_lrat, compact_lrat, compact_lrat_gz)
    if receipt["verdict"] != "UNSAT":
        if any(path is not None for path in proof_paths):
            raise ReceiptError("SAT receipt cannot bind LRAT artifacts")
        return
    if any(path is None for path in proof_paths):
        raise ReceiptError("UNSAT artifact verification requires all LRAT forms")
    assert raw_lrat is not None and compact_lrat is not None
    assert compact_lrat_gz is not None
    checks = (
        (raw_lrat, "raw_lrat_sha256", "raw_lrat_bytes"),
        (compact_lrat, "compact_lrat_sha256", "compact_lrat_bytes"),
        (compact_lrat_gz, "compact_lrat_gz_sha256", "compact_lrat_gz_bytes"),
    )
    for path, sha_key, bytes_key in checks:
        digest, size = file_identity(path)
        if digest != receipt[sha_key] or size != int(receipt[bytes_key]):
            raise ReceiptError(f"artifact identity mismatch for {sha_key}")
    decompressed = hashlib.sha256()
    try:
        with gzip.open(compact_lrat_gz, "rb") as stream:
            for chunk in iter(lambda: stream.read(1 << 20), b""):
                decompressed.update(chunk)
    except (OSError, EOFError) as error:
        raise ReceiptError("invalid compact LRAT gzip artifact") from error
    if decompressed.hexdigest() != receipt["compact_lrat_sha256"]:
        raise ReceiptError("compact gzip content differs from compact LRAT")


def parse(line: str, expected_jobs: set[str] | None = None,
          expected_manifest_sha256: str | None = None) -> dict[str, str]:
    fields = line.split()
    if len(fields) < 4:
        raise ReceiptError("terminal receipt is too short")
    timestamp, job, verdict, *metadata_fields = fields
    try:
        parsed_time = datetime.fromisoformat(timestamp.replace("Z", "+00:00"))
    except ValueError as error:
        raise ReceiptError("invalid terminal timestamp") from error
    if not timestamp.endswith("Z") or parsed_time.tzinfo is None:
        raise ReceiptError("terminal timestamp must be UTC with a Z suffix")
    if JOB_RE.fullmatch(job) is None:
        raise ReceiptError(f"malformed job id: {job}")
    if expected_jobs is not None and job not in expected_jobs:
        raise ReceiptError(f"job is absent from the selected manifest: {job}")
    if verdict not in {"UNSAT", "SAT"}:
        raise ReceiptError(f"nonterminal verdict in ledger: {verdict}")

    metadata: dict[str, str] = {}
    for field in metadata_fields:
        if field.count("=") != 1:
            raise ReceiptError(f"malformed metadata field: {field}")
        key, value = field.split("=", 1)
        if not key or not value:
            raise ReceiptError(f"empty metadata key or value: {field}")
        if key in metadata:
            raise ReceiptError(f"duplicate metadata key: {key}")
        metadata[key] = value

    required = COMMON | (UNSAT if verdict == "UNSAT" else SAT)
    missing = required - set(metadata)
    if missing:
        raise ReceiptError(f"missing terminal metadata: {sorted(missing)}")
    if metadata["schema"] != SCHEMA:
        raise ReceiptError(f"unsupported terminal schema: {metadata['schema']}")
    if metadata["provenance"] not in {"fresh", "legacy-migration"}:
        raise ReceiptError(f"invalid provenance: {metadata['provenance']}")
    if metadata["mode"] not in {"quick", "slow"}:
        raise ReceiptError(f"invalid mode: {metadata['mode']}")
    if metadata["generator_kind"] not in {"root", "nested", "third"}:
        raise ReceiptError(f"invalid generator kind: {metadata['generator_kind']}")
    expected_generator = ("third" if ".third." in job else
                          "nested" if ".nested." in job else "root")
    if metadata["generator_kind"] != expected_generator:
        raise ReceiptError(
            f"job requires generator_kind={expected_generator}, got "
            f"{metadata['generator_kind']}"
        )
    if (expected_manifest_sha256 is not None and
            metadata["manifest_sha256"] != expected_manifest_sha256):
        raise ReceiptError("receipt does not bind the supplied job manifest")
    for key in HASH_FIELDS & set(metadata):
        if SHA256_RE.fullmatch(metadata[key]) is None:
            raise ReceiptError(f"invalid SHA256 in {key}")
    for key in NONNEGATIVE_INTEGER_FIELDS & set(metadata):
        try:
            value = int(metadata[key])
        except ValueError as error:
            raise ReceiptError(f"non-integer {key}") from error
        if value < 0:
            raise ReceiptError(f"negative {key}")
    if ("lean_image_digest" in metadata and
            re.fullmatch(r"sha256:[0-9a-f]{64}",
                         metadata["lean_image_digest"]) is None):
        raise ReceiptError("invalid Lean image digest")
    if int(metadata["solve_s"]) > int(metadata["cap_s"]) + 60:
        raise ReceiptError("solve time exceeds cap plus shutdown allowance")
    if metadata["provenance"] == "fresh" and int(metadata["solve_peak_rss_kb"]) <= 0:
        raise ReceiptError("fresh receipt requires positive solve_peak_rss_kb")
    if (metadata["provenance"] == "legacy-migration" and
            int(metadata["solve_peak_rss_kb"]) != 0):
        raise ReceiptError(
            "legacy migration must mark unavailable solve peak RSS as zero"
        )

    if verdict == "UNSAT":
        if int(metadata["rc"]) != 20:
            raise ReceiptError("UNSAT receipt must have rc=20")
        expected_values = {
            "trim": "VERIFIED", "lrat_kind": "compact-v1",
            "native_lratcheck": "VERIFIED", "lean_lratreplay": "VERIFIED",
            "upload": "uploaded",
        }
        for key, expected in expected_values.items():
            if metadata[key] != expected:
                raise ReceiptError(f"UNSAT receipt requires {key}={expected}")
        if metadata["remote_sha256"] != metadata["compact_lrat_gz_sha256"]:
            raise ReceiptError("remote SHA does not match uploaded compact proof")
        for key in ("raw_lrat_bytes", "compact_lrat_bytes",
                    "compact_lrat_gz_bytes", "cnf_bytes", "maxvar"):
            if int(metadata[key]) <= 0:
                raise ReceiptError(f"UNSAT receipt requires positive {key}")
    else:
        if metadata["provenance"] != "fresh":
            raise ReceiptError("SAT receipt cannot use legacy-migration provenance")
        if int(metadata["rc"]) != 10 or int(metadata["reproduce_rc"]) != 10:
            raise ReceiptError("SAT receipt requires initial and reproduction rc=10")
        if metadata["model"] != "VERIFIED":
            raise ReceiptError("SAT receipt requires model=VERIFIED")

    return {"timestamp": timestamp, "job": job, "verdict": verdict, **metadata}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("receipt", type=Path)
    parser.add_argument("--expected-job")
    parser.add_argument("--manifest", type=Path)
    parser.add_argument("--expected-manifest-sha256")
    parser.add_argument("--solved-cnf", type=Path)
    parser.add_argument("--raw-lrat", type=Path)
    parser.add_argument("--compact-lrat", type=Path)
    parser.add_argument("--compact-lrat-gz", type=Path)
    args = parser.parse_args()
    lines = args.receipt.read_text().splitlines()
    if len(lines) != 1:
        parser.error("receipt must contain exactly one line")
    expected = {args.expected_job} if args.expected_job else None
    manifest_sha = None
    if args.manifest is not None:
        manifest_jobs, manifest_sha = manifest_identity(
            args.manifest, args.expected_manifest_sha256)
        expected = manifest_jobs if expected is None else expected & manifest_jobs
        if not expected:
            parser.error("--expected-job is absent from --manifest")
    elif args.expected_manifest_sha256 is not None:
        parser.error("--expected-manifest-sha256 requires --manifest")
    result = parse(lines[0], expected, manifest_sha)
    proof_args = (args.raw_lrat, args.compact_lrat, args.compact_lrat_gz)
    if args.solved_cnf is None:
        if any(path is not None for path in proof_args):
            parser.error("LRAT artifact flags require --solved-cnf")
    else:
        validate_artifacts(result, args.solved_cnf, *proof_args)
    print(f"TERMINAL RECEIPT VERIFIED {result['job']} {result['verdict']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
