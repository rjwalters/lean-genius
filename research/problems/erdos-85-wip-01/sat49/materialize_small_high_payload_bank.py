#!/usr/bin/env python3
"""Materialize the exact 406 retained compact proofs and replay-audit bank."""

from __future__ import annotations

import argparse, gzip, hashlib, importlib.util, json, os, re, shutil, subprocess, sys, tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent


def imported(name, file):
    spec = importlib.util.spec_from_file_location(name, HERE / file)
    module = importlib.util.module_from_spec(spec); assert spec.loader is not None
    spec.loader.exec_module(module); return module


TERMINAL = imported("terminal", "validate_sat49_terminal_ledger.py")
GENERATOR = imported("generator", "generate_small_high_cube_lean_module.py")
AGGREGATES = imported("aggregates", "build_small_high_cell_aggregate_receipts.py")
SCHEMA = "erdos85-small-high-payload-bank-v1"
AUDIT_SCHEMA = "erdos85-small-high-rich-replay-audit-v1"
ROOT_MANIFEST_SHA256 = "05381a1cf5e80eb480b6e78c4a8dada2573c1cf2f0c55d9ac0bcc4367e3bca76"
ROOT_GENERATOR_SHA256 = "a845cb9f6bf1d6046c58aefe9cd6cdd66e80e0fd3670629ba650e9578fe5cb7e"
QUEUE_RECEIPT_SHA256 = "fa07876764990816f4d7a5940b09958c33d86676edcc3cddcbabad32b482d103"
QUEUE_SHA256 = "91cd2b14a3d0f5a3b9d30d94a4765928a885da74f428a754aadcda5c9ada504b"
WORKER_RECEIPT_SHA256 = "35d1f8a4f616630ca60cd37ee364d9bb81080299695f11d0a6fbac11656db108"
WORKER_SHA256 = "137e57dc3884fc2f61986cb0ed56762e3fe93708331e8f600fc83aa535e5d22a"
S3_PREFIX = "s3://2am-erdos85-certs/sat49/campaign-20260825/tierA"
IMAGE = "lean4-arm64@sha256:a5ca6c4e3328a1832d5f9b814ab7c1e35616903b3956341962a5b1a96fb6dff6"
LRATREPLAY_SHA256 = "37aad1d5c64a75fcb68e1ea587b2080b06c157a19c883b01d145b28b891c428c"
LEDGER_PINS = {"generator_kind":"root", "generator_sha256":ROOT_GENERATOR_SHA256,
    "kissat_sha256":"05d6f3e9c402a1fe8853b0746e384e1b3d1c4a550e255f11daa2461d279aa848",
    "drat_trim_sha256":"f58f63b0f76945d4c4c9ff6e87afaf870f579e67c0f7cca589492df8fc7ebd47",
    "lrat_check_sha256":"bd7eb8052623525814a0a37502b47f05375d9d9dfaf96ddc2fcd858958517cea",
    "compactor_sha256":"50e413519b248b2c58a68688f6e11f559c255760c0a91313358bf284aae7aa20",
    "lratreplay_sha256":LRATREPLAY_SHA256,
    "lean_image_digest":"sha256:a5ca6c4e3328a1832d5f9b814ab7c1e35616903b3956341962a5b1a96fb6dff6"}


def canonical(value):
    return (json.dumps(value, ensure_ascii=True, allow_nan=False,
                       sort_keys=True, separators=(",", ":")) + "\n").encode("ascii")


def sha(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""): h.update(block)
    return h.hexdigest()


def require_file(path, pin, label):
    if not path.is_absolute() or path.is_symlink() or not path.is_file() or sha(path) != pin:
        raise ValueError(f"{label} path/hash mismatch")


def jobs(manifest):
    result = []
    for _, cell, _ in AGGREGATES.CELLS:
        expected = AGGREGATES.expected_job_ids(cell)
        actual = [row.get("id") for row in manifest.get("cells", {}).get(cell, {}).get("jobs", [])]
        if actual != expected: raise ValueError(f"{cell}: manifest order/set mismatch")
        result.extend(expected)
    if len(result) != 406 or len(set(result)) != 406: raise ValueError("not exact 406 jobs")
    return result


def lineage(work_root):
    path = work_root / "lineage.json"
    value = json.loads(path.read_text())
    expected = {"root_manifest_sha256": ROOT_MANIFEST_SHA256,
                "queue_receipt_sha256": QUEUE_RECEIPT_SHA256,
                "queue_sha256": QUEUE_SHA256,
                "worker_receipt_sha256": WORKER_RECEIPT_SHA256,
                "worker_sha256": WORKER_SHA256}
    if path.is_symlink() or path.read_bytes() != canonical(value) or any(value.get(k) != v for k, v in expected.items()):
        raise ValueError("work-root lineage mismatch")
    return value


def build(root_manifest: Path, work_root: Path, output: Path,
          materialize, fetch, replay) -> None:
    materializer_sha256 = sha(Path(__file__))
    require_file(root_manifest, ROOT_MANIFEST_SHA256, "root manifest")
    if not work_root.is_absolute() or work_root.is_symlink() or not work_root.is_dir():
        raise ValueError("work root must be absolute real directory")
    if not output.is_absolute() or output.is_symlink() or output.exists() or not output.parent.is_dir() or output.parent.is_symlink():
        raise ValueError("output must be absent under an existing real directory")
    lineage_value = lineage(work_root)
    manifest = json.loads(root_manifest.read_text())
    if root_manifest.read_bytes() != canonical(manifest): raise ValueError("noncanonical root manifest")
    ordered_jobs = jobs(manifest)
    actual_dirs = {path.name for path in work_root.iterdir() if path.is_dir()}
    if actual_dirs != set(ordered_jobs): raise ValueError("work root lacks exact 406 job directories")
    if any((work_root/job).is_symlink() for job in ordered_jobs): raise ValueError("symlinked job directory")
    helper_sources = [{"source": path.name, "sha256": sha(path)} for path in (
        HERE / "validate_sat49_terminal_ledger.py", HERE / "generate_small_high_cube_lean_module.py",
        HERE / "build_small_high_cell_aggregate_receipts.py")]
    with tempfile.TemporaryDirectory(prefix="small-high-bank-stage-", dir=output.parent) as raw:
        stage = Path(raw); payload_rows, audits, payload_paths = [], [], []
        expected_jobs, _ = TERMINAL.manifest_identity(root_manifest, ROOT_MANIFEST_SHA256)
        for job in ordered_jobs:
            ledger = work_root / job / "ledger.line"
            if ledger.is_symlink() or not ledger.is_file(): raise ValueError(f"{job}: missing terminal ledger")
            ledger_raw = ledger.read_bytes()
            if ledger_raw.count(b"\n") != 1 or not ledger_raw.endswith(b"\n"):
                raise ValueError(f"{job}: terminal ledger is not one canonical line")
            parsed = TERMINAL.parse(ledger_raw[:-1].decode(), expected_jobs, ROOT_MANIFEST_SHA256)
            if (parsed["job"] != job or parsed["verdict"] != "UNSAT"
                    or any(parsed.get(k) != v for k,v in LEDGER_PINS.items())):
                raise ValueError(f"{job}: terminal or approved tool/image pins mismatch")
            cnf, gz = stage / f"{job}.cnf", stage / f"{job}.lrat.gz"
            materialize(job, cnf); fetch(job, gz)
            if cnf.is_symlink() or gz.is_symlink() or not cnf.is_file() or not gz.is_file():
                raise ValueError(f"{job}: adapters did not create regular artifacts")
            TERMINAL.validate_compact_artifacts(parsed, cnf, gz)
            if sha(cnf) != parsed["emitted_cnf_sha256"]:
                raise ValueError(f"{job}: rematerialized CNF differs from emitted identity")
            payload = stage / f"{job}.lrat"
            with gzip.open(gz, "rb") as source, payload.open("xb") as target:
                shutil.copyfileobj(source, target); target.flush(); os.fsync(target.fileno())
            replay_result = replay(job, cnf, payload)
            replay_fields = {"accepted","accepted_marker","command_identity_sha256","image",
                "lratreplay_sha256","rc","stderr_sha256","stdout_sha256"}
            if set(replay_result) != replay_fields or replay_result["accepted"] is not True:
                raise ValueError(f"{job}: independent replay failed or malformed")
            if (replay_result["accepted_marker"] != "LRAT accepted: true"
                    or replay_result["image"] != IMAGE or replay_result["lratreplay_sha256"] != LRATREPLAY_SHA256
                    or type(replay_result["rc"]) is not int or replay_result["rc"] != 0
                    or any(not isinstance(replay_result[key], str) or re.fullmatch(r"[0-9a-f]{64}",replay_result[key]) is None
                   for key in ("command_identity_sha256", "stdout_sha256", "stderr_sha256"))):
                raise ValueError(f"{job}: replay identities are malformed")
            replay_evidence = {"job_id":job,"schema":"erdos85-small-high-replay-evidence-v1",**replay_result}
            replay_path = stage/f"{job}.replay.json"; replay_path.write_bytes(canonical(replay_evidence))
            key = f"{S3_PREFIX}/{job}.compact-v1.lrat.gz"
            payload_rows.append({"job_id": job, "path": str(output / f"{job}.lrat"),
                                 "sha256": parsed["compact_lrat_sha256"]})
            audits.append({"cnf_sha256": parsed["solved_cnf_sha256"], "job_id": job,
                "ledger_sha256": sha(ledger), "payload_sha256": sha(payload),
                "retained_gzip_sha256": sha(gz), "replay_evidence":f"{job}.replay.json",
                "replay_evidence_sha256":sha(replay_path), "s3_key": key, **replay_result})
            payload_paths.append((job, payload))
        payload_manifest = {"payloads": payload_rows,
            "root_manifest_sha256": ROOT_MANIFEST_SHA256, "schema": GENERATOR.PAYLOAD_SCHEMA}
        replay_audit = {"jobs": audits, "lineage": lineage_value,
                        "schema": AUDIT_SCHEMA}
        receipt = {"helper_sources": helper_sources, "jobs": 406,
            "materializer_sha256":materializer_sha256,
            "materializer_source":"research/problems/erdos-85-wip-01/sat49/materialize_small_high_payload_bank.py",
            "payload_manifest_sha256": hashlib.sha256(canonical(payload_manifest)).hexdigest(),
            "replay_audit_sha256": hashlib.sha256(canonical(replay_audit)).hexdigest(),
            "root_manifest": str(root_manifest), "root_manifest_sha256": ROOT_MANIFEST_SHA256,
            "schema": SCHEMA, "work_root": str(work_root)}
        # Recheck all evidence immediately before any output publication.
        if lineage(work_root) != lineage_value or sha(root_manifest) != ROOT_MANIFEST_SHA256:
            raise ValueError("lineage drift before publication")
        for audit in audits:
            if sha(work_root / audit["job_id"] / "ledger.line") != audit["ledger_sha256"]:
                raise ValueError("ledger drift before publication")
        if helper_sources != [{"source": path.name, "sha256": sha(path)} for path in (
                HERE / "validate_sat49_terminal_ledger.py", HERE / "generate_small_high_cube_lean_module.py",
                HERE / "build_small_high_cell_aggregate_receipts.py")]:
            raise ValueError("helper source drift before publication")
        output.mkdir(exist_ok=False)
        for job, source_path in payload_paths:
            with source_path.open("rb") as source, (output / f"{job}.lrat").open("xb") as stream:
                shutil.copyfileobj(source,stream); stream.flush(); os.fsync(stream.fileno())
            replay_source=stage/f"{job}.replay.json"
            with replay_source.open("rb") as source,(output/f"{job}.replay.json").open("xb") as stream:
                shutil.copyfileobj(source,stream); stream.flush(); os.fsync(stream.fileno())
        for name, value in (("payloads.json", payload_manifest), ("replay-audit.json", replay_audit)):
            with (output / name).open("xb") as stream:
                stream.write(canonical(value)); stream.flush(); os.fsync(stream.fileno())
        for row in payload_rows:
            if sha(Path(row["path"])) != row["sha256"]: raise ValueError("published payload drift")
        if (sha(Path(__file__)) != materializer_sha256 or lineage(work_root) != lineage_value
                or sha(root_manifest) != ROOT_MANIFEST_SHA256
                or helper_sources != [{"source": path.name, "sha256": sha(path)} for path in (
                    HERE/"validate_sat49_terminal_ledger.py",HERE/"generate_small_high_cube_lean_module.py",
                    HERE/"build_small_high_cell_aggregate_receipts.py")]
                or sha(output/"payloads.json") != receipt["payload_manifest_sha256"]
                or sha(output/"replay-audit.json") != receipt["replay_audit_sha256"]):
            raise ValueError("source/input/output drift before receipt")
        for audit in audits:
            if (sha(work_root/audit["job_id"]/"ledger.line") != audit["ledger_sha256"]
                    or sha(output/audit["replay_evidence"]) != audit["replay_evidence_sha256"]):
                raise ValueError("ledger/replay evidence drift before receipt")
        with (output / "receipt.json").open("xb") as stream:
            stream.write(canonical(receipt)); stream.flush(); os.fsync(stream.fileno())
        descriptor = os.open(output, os.O_RDONLY)
        try: os.fsync(descriptor)
        finally: os.close(descriptor)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root-manifest", type=Path, required=True)
    parser.add_argument("--work-root", type=Path, required=True)
    parser.add_argument("--root-generator", type=Path, required=True)
    parser.add_argument("--root-generator-sha256", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    require_file(args.root_generator, ROOT_GENERATOR_SHA256, "root generator")
    if args.root_generator_sha256 != ROOT_GENERATOR_SHA256:
        parser.error("root generator CLI pin differs from approved constant")
    def materialize(job, output):
        subprocess.run([sys.executable, str(args.root_generator), "materialize",
            "--manifest", str(args.root_manifest), "--job", job, "--output", str(output)], check=True)
    def fetch(job, output):
        subprocess.run(["aws", "s3", "cp", "--only-show-errors",
            f"{S3_PREFIX}/{job}.compact-v1.lrat.gz", str(output)],
            env={**os.environ, "AWS_PROFILE":"2am-admin"}, check=True)
    def replay(job, cnf, payload):
        root = cnf.parent
        command = ["docker","run","--rm","-v",f"{root}:/data","--entrypoint","/bin/sh",IMAGE,"-c",
            "sha256sum /cache/bin/lratreplay; /cache/bin/lratreplay \"$1\" \"$2\"", "replay",
            f"/data/{cnf.name}", f"/data/{payload.name}"]
        result = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        lines = result.stdout.decode(errors="replace").splitlines()
        pin_ok = bool(lines) and lines[0].split(maxsplit=1)[0] == LRATREPLAY_SHA256
        accepted = result.returncode == 0 and pin_ok and lines[-1].strip() == "LRAT accepted: true"
        identity = {"command":command,"image":IMAGE,"lratreplay_sha256":LRATREPLAY_SHA256}
        return {"accepted":accepted,"accepted_marker":"LRAT accepted: true",
            "command_identity_sha256":hashlib.sha256(canonical(identity)).hexdigest(),
            "image":IMAGE,"lratreplay_sha256":LRATREPLAY_SHA256,"rc":result.returncode,
            "stdout_sha256":hashlib.sha256(result.stdout).hexdigest(),
            "stderr_sha256":hashlib.sha256(result.stderr).hexdigest()}
    build(args.root_manifest,args.work_root,args.output,materialize,fetch,replay)
    print(f"WROTE {args.output} jobs=406")


if __name__ == "__main__": main()
