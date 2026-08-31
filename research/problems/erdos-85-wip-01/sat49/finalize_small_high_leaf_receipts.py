#!/usr/bin/env python3
"""Bind a reviewed generated module to the exact 406 rich replay results."""

from __future__ import annotations

import argparse, hashlib, importlib.util, json, os, re, subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent


def imported(name, filename):
    spec = importlib.util.spec_from_file_location(name, HERE / filename)
    module = importlib.util.module_from_spec(spec); assert spec.loader is not None
    spec.loader.exec_module(module); return module


BANK = imported("payload_bank", "materialize_small_high_payload_bank.py")
GENERATOR = imported("cube_generator", "generate_small_high_cube_lean_module.py")
AGGREGATES = imported("aggregates", "build_small_high_cell_aggregate_receipts.py")
SCHEMA = "erdos85-small-high-final-leaf-bank-v1"
REPLAY_SCHEMA = "erdos85-small-high-leaf-replay-v2"
LEAF_SCHEMA = "erdos85-small-high-leaf-evidence-v2"
SOURCE_MODULE = GENERATOR.SOURCE_MODULE
MODULE_REPO_PATH = "proofs/Proofs/Generated/Erdos85OrderFortyNineSmallHighCertificates.lean"
GENERATOR_SOURCE = "research/problems/erdos-85-wip-01/sat49/generate_small_high_cube_lean_module.py"
LINEAGE_SCHEMA = "erdos85-tierA-root-lineage-v1"
FREIGHT_RECEIPT_SHA256 = "6084315bc86ad262533a660aad308639d1d087666b965df47569627c6adf2897"
CONTROLLER_SOURCE = "research/problems/erdos-85-wip-01/sat49/run_tierA_root_queue.py"
SHA = re.compile(r"[0-9a-f]{64}"); COMMIT = re.compile(r"[0-9a-f]{40}"); REVIEW = re.compile(r"#?[1-9][0-9]*")


def canonical(value):
    return (json.dumps(value, ensure_ascii=True, allow_nan=False,
                       sort_keys=True, separators=(",", ":")) + "\n").encode("ascii")


def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()


def regular(path, label):
    if not path.is_absolute() or path.is_symlink() or not path.is_file(): raise ValueError(f"{label} must be absolute regular non-symlink")


def read_canonical(path, pin, label):
    regular(path,label)
    if SHA.fullmatch(pin) is None or sha(path)!=pin: raise ValueError(f"{label} SHA mismatch")
    value=json.loads(path.read_text())
    if path.read_bytes()!=canonical(value): raise ValueError(f"{label} is noncanonical")
    return value


def ordered_jobs(): return [job for _,cell,_ in AGGREGATES.CELLS for job in AGGREGATES.expected_job_ids(cell)]


def fsync_dir(path):
    descriptor=os.open(path,os.O_RDONLY)
    try: os.fsync(descriptor)
    finally: os.close(descriptor)


def committed_bytes(repo,module_repo_path,commit):
    if (not repo.is_absolute() or repo.is_symlink() or not repo.is_dir()
            or module_repo_path!=MODULE_REPO_PATH or COMMIT.fullmatch(commit) is None):
        raise ValueError("repository/module commit identity invalid")
    return subprocess.run(["git","show",f"{commit}:{MODULE_REPO_PATH}"],cwd=repo,
                          stdout=subprocess.PIPE,check=True).stdout


def build(bank_dir:Path, bank_receipt_sha256:str, module:Path, module_receipt:Path,
          module_receipt_sha256:str,
          module_commit:str, review_id:str, output:Path, committed_module:bytes)->None:
    finalizer_sha=sha(Path(__file__))
    if not bank_dir.is_absolute() or bank_dir.is_symlink() or not bank_dir.is_dir(): raise ValueError("bank directory invalid")
    if not output.is_absolute() or output.is_symlink() or output.exists() or not output.parent.is_dir() or output.parent.is_symlink(): raise ValueError("output invalid")
    if COMMIT.fullmatch(module_commit) is None or REVIEW.fullmatch(review_id) is None: raise ValueError("commit/review invalid")
    bank_receipt=read_canonical(bank_dir/"receipt.json",bank_receipt_sha256,"bank receipt")
    bank_fields={"helper_sources","jobs","materializer_sha256","materializer_source",
        "payload_manifest_sha256","replay_audit_sha256","root_manifest",
        "root_manifest_sha256","schema","work_root"}
    if (set(bank_receipt)!=bank_fields or bank_receipt.get("schema")!=BANK.SCHEMA or bank_receipt.get("jobs")!=406
            or bank_receipt.get("root_manifest_sha256")!=BANK.ROOT_MANIFEST_SHA256):
        raise ValueError("bank receipt identity mismatch")
    payloads=read_canonical(bank_dir/"payloads.json",bank_receipt["payload_manifest_sha256"],"payload manifest")
    audit=read_canonical(bank_dir/"replay-audit.json",bank_receipt["replay_audit_sha256"],"replay audit")
    jobs=ordered_jobs()
    lineage=audit.get("lineage"); lineage_fields={"schema","work_root","worker_sha256",
        "worker_receipt_sha256","queue_receipt_sha256","queue_sha256","root_manifest_sha256",
        "freight_receipt_sha256","controller_git_commit","controller_source","controller_sha256"}
    fixed_lineage={"root_manifest_sha256":BANK.ROOT_MANIFEST_SHA256,
        "queue_receipt_sha256":BANK.QUEUE_RECEIPT_SHA256,"queue_sha256":BANK.QUEUE_SHA256,
        "worker_receipt_sha256":BANK.WORKER_RECEIPT_SHA256,"worker_sha256":BANK.WORKER_SHA256}
    payload_rows=payloads.get("payloads",[]); audit_rows=audit.get("jobs",[])
    payload_row_fields={"job_id","path","sha256"}
    audit_row_fields={"accepted","accepted_marker","cnf_sha256","command_identity_sha256",
        "image","job_id","ledger_sha256","lratreplay_sha256","payload_sha256","rc",
        "replay_evidence","replay_evidence_sha256","retained_gzip_sha256","s3_key",
        "stderr_sha256","stdout_sha256"}
    if (set(payloads)!={"payloads","root_manifest_sha256","schema"}
            or set(audit)!={"jobs","lineage","schema"}
            or [row.get("job_id") for row in payload_rows]!=jobs
            or any(set(row)!=payload_row_fields for row in payload_rows)
            or [row.get("job_id") for row in audit_rows]!=jobs
            or any(set(row)!=audit_row_fields for row in audit_rows)
            or payloads.get("root_manifest_sha256")!=BANK.ROOT_MANIFEST_SHA256
            or payloads.get("schema")!=GENERATOR.PAYLOAD_SCHEMA
            or audit.get("schema")!=BANK.AUDIT_SCHEMA
            or not isinstance(lineage,dict) or set(lineage)!=lineage_fields
            or any(lineage.get(k)!=v for k,v in fixed_lineage.items())
            or lineage.get("schema")!=LINEAGE_SCHEMA
            or not Path(str(lineage.get("work_root"))).is_absolute()
            or lineage.get("work_root")!=bank_receipt.get("work_root")
            or lineage.get("freight_receipt_sha256")!=FREIGHT_RECEIPT_SHA256
            or lineage.get("controller_source")!=CONTROLLER_SOURCE
            or COMMIT.fullmatch(str(lineage.get("controller_git_commit"))) is None
            or any(SHA.fullmatch(str(lineage.get(k))) is None
                   for k in ("freight_receipt_sha256","controller_sha256"))):
        raise ValueError("bank 406 order/schema/lineage mismatch")
    regular(module,"generated module"); module_raw=module.read_bytes()
    if module_raw!=committed_module: raise ValueError("module bytes differ from reviewed commit")
    module_receipt_value=read_canonical(module_receipt,module_receipt_sha256,"module receipt")
    module_receipt_fields={"generator_sha256","generator_source","certificate_dir","include_root",
        "jobs","module","module_bytes","module_sha256","payload_identity_sha256",
        "payload_manifest","payload_manifest_sha256","root_manifest","root_manifest_sha256",
        "schema","source_module"}
    if (set(module_receipt_value)!=module_receipt_fields
            or module_receipt_value.get("schema")!=GENERATOR.MODULE_RECEIPT_SCHEMA
            or module_receipt_value.get("source_module")!=SOURCE_MODULE
            or module_receipt_value.get("jobs")!=406
            or module_receipt_value.get("module")!=str(module)
            or module_receipt_value.get("module_bytes")!=len(module_raw)
            or module_receipt_value.get("module_sha256")!=hashlib.sha256(module_raw).hexdigest()
            or module_receipt_value.get("payload_manifest")!=str(bank_dir/"payloads.json")
            or module_receipt_value.get("payload_manifest_sha256")!=bank_receipt["payload_manifest_sha256"]
            or module_receipt_value.get("certificate_dir")!=str(bank_dir)
            or module_receipt_value.get("include_root")!=str(bank_dir)
            or module_receipt_value.get("root_manifest")!=bank_receipt["root_manifest"]
            or module_receipt_value.get("root_manifest_sha256")!=BANK.ROOT_MANIFEST_SHA256
            or module_receipt_value.get("generator_source")!=GENERATOR_SOURCE
            or module_receipt_value.get("generator_sha256")!=sha(HERE/"generate_small_high_cube_lean_module.py")
            or module_receipt_value.get("payload_identity_sha256")!=hashlib.sha256(canonical(payload_rows)).hexdigest()):
        raise ValueError("generated module receipt mismatch")
    payload_by_job={row["job_id"]:row for row in payloads["payloads"]}; audit_by_job={row["job_id"]:row for row in audit["jobs"]}
    finalized=[]
    for job in jobs:
        theorem=f"Erdos85.{GENERATOR.lean_stem(job)}_unsat"; row=payload_by_job[job]; event=audit_by_job[job]
        payload=Path(row["path"]); regular(payload,f"{job} payload")
        if payload != bank_dir/f"{job}.lrat": raise ValueError(f"{job}: payload path mismatch")
        hash_fields=("cnf_sha256","command_identity_sha256","ledger_sha256","payload_sha256",
                     "replay_evidence_sha256","retained_gzip_sha256","stderr_sha256","stdout_sha256")
        if (SHA.fullmatch(str(row.get("sha256"))) is None
                or any(SHA.fullmatch(str(event.get(field))) is None for field in hash_fields)
                or event.get("s3_key")!=f"{BANK.S3_PREFIX}/{job}.compact-v1.lrat.gz"
                or sha(payload)!=row["sha256"] or event["payload_sha256"]!=row["sha256"]):
            raise ValueError(f"{job}: payload/audit identity mismatch")
        if event.get("replay_evidence") != f"{job}.replay.json": raise ValueError(f"{job}: replay evidence path mismatch")
        evidence=read_canonical(bank_dir/event["replay_evidence"],event["replay_evidence_sha256"],f"{job} replay evidence")
        rich_fields=("accepted","accepted_marker","command_identity_sha256","image",
                     "lratreplay_sha256","rc","stderr_sha256","stdout_sha256")
        if (set(evidence)!={"job_id","schema",*rich_fields}
                or evidence.get("schema")!="erdos85-small-high-replay-evidence-v1"
                or evidence.get("job_id")!=job
                or any(evidence.get(field)!=event.get(field) for field in rich_fields)
                or evidence.get("accepted") is not True or evidence.get("accepted_marker")!="LRAT accepted: true"
                or evidence.get("rc")!=0 or type(evidence.get("rc")) is not int
                or evidence.get("image")!=BANK.IMAGE or evidence.get("lratreplay_sha256")!=BANK.LRATREPLAY_SHA256
                or any(SHA.fullmatch(str(evidence.get(field))) is None
                       for field in ("command_identity_sha256","stderr_sha256","stdout_sha256"))):
            raise ValueError(f"{job}: rich replay identity mismatch")
        replay={"cnf_sha256":event["cnf_sha256"],"commit":module_commit,
            "compact_lrat_sha256":row["sha256"],"image":evidence["image"],"job_id":job,
            "lratreplay_sha256":evidence["lratreplay_sha256"],"materializer_receipt_sha256":bank_receipt_sha256,
            "replay_audit_sha256":bank_receipt["replay_audit_sha256"],"replay_evidence_sha256":event["replay_evidence_sha256"],
            "replay_verdict":"VERIFIED","schema":REPLAY_SCHEMA,"source_module":SOURCE_MODULE,"theorem":theorem}
        replay_raw=canonical(replay); replay_sha=hashlib.sha256(replay_raw).hexdigest()
        leaf={"cnf_sha256":event["cnf_sha256"],"commit":module_commit,
            "compact_lrat_sha256":row["sha256"],"hypothesis":theorem,"job_id":job,
            "materializer_receipt_sha256":bank_receipt_sha256,"module_receipt_sha256":module_receipt_sha256,
            "queue_receipt_sha256":BANK.QUEUE_RECEIPT_SHA256,"queue_sha256":BANK.QUEUE_SHA256,
            "replay_audit_sha256":bank_receipt["replay_audit_sha256"],"replay_evidence_sha256":event["replay_evidence_sha256"],
            "replay_receipt_path":str(output/"replay-receipts"/f"{job}.json"),"replay_receipt_sha256":replay_sha,
            "review_id":review_id,"root_manifest_sha256":BANK.ROOT_MANIFEST_SHA256,"schema":LEAF_SCHEMA,
            "source_module":SOURCE_MODULE,"theorem":theorem,"worker_receipt_sha256":BANK.WORKER_RECEIPT_SHA256,"worker_sha256":BANK.WORKER_SHA256}
        finalized.append((job,replay_raw,canonical(leaf)))
    # Recheck immutable inputs before publication.
    if sha(Path(__file__))!=finalizer_sha or sha(module)!=hashlib.sha256(module_raw).hexdigest() or sha(bank_dir/"receipt.json")!=bank_receipt_sha256: raise ValueError("input drift before publication")
    output.mkdir(); leaves=output/"leaf-receipts"; replays=output/"replay-receipts"; leaves.mkdir(); replays.mkdir()
    index=[]
    for job,replay_raw,leaf_raw in finalized:
        for path,raw in ((replays/f"{job}.json",replay_raw),(leaves/f"{job}.receipt.json",leaf_raw)):
            with path.open("xb") as stream: stream.write(raw); stream.flush(); os.fsync(stream.fileno())
        index.append({"job_id":job,"leaf_receipt_sha256":hashlib.sha256(leaf_raw).hexdigest(),"replay_receipt_sha256":hashlib.sha256(replay_raw).hexdigest()})
    index_value={"jobs":index,"schema":SCHEMA}; index_raw=canonical(index_value)
    with (output/"index.json").open("xb") as stream: stream.write(index_raw); stream.flush(); os.fsync(stream.fileno())
    fsync_dir(leaves); fsync_dir(replays); fsync_dir(output)
    if (sha(Path(__file__))!=finalizer_sha or sha(module)!=hashlib.sha256(module_raw).hexdigest()
            or sha(module_receipt)!=module_receipt_sha256
            or sha(bank_dir/"receipt.json")!=bank_receipt_sha256
            or sha(bank_dir/"payloads.json")!=bank_receipt["payload_manifest_sha256"]
            or sha(bank_dir/"replay-audit.json")!=bank_receipt["replay_audit_sha256"]):
        raise ValueError("input drift before receipt")
    for job,replay_raw,leaf_raw in finalized:
        row=payload_by_job[job]; event=audit_by_job[job]
        if (sha(bank_dir/f"{job}.lrat")!=row["sha256"]
                or sha(bank_dir/f"{job}.replay.json")!=event["replay_evidence_sha256"]
                or sha(replays/f"{job}.json")!=hashlib.sha256(replay_raw).hexdigest()
                or sha(leaves/f"{job}.receipt.json")!=hashlib.sha256(leaf_raw).hexdigest()):
            raise ValueError(f"{job}: input/output drift before receipt")
    if sha(output/"index.json")!=hashlib.sha256(index_raw).hexdigest(): raise ValueError("index drift before receipt")
    receipt={"bank_receipt_sha256":bank_receipt_sha256,"finalizer_sha256":finalizer_sha,
        "index_sha256":hashlib.sha256(index_raw).hexdigest(),"jobs":406,"module_commit":module_commit,
        "leaf_receipts":str(leaves),"module_receipt_sha256":module_receipt_sha256,
        "module_sha256":hashlib.sha256(module_raw).hexdigest(),"replay_receipts":str(replays),
        "review_id":review_id,"schema":SCHEMA}
    with (output/"receipt.json").open("xb") as stream: stream.write(canonical(receipt)); stream.flush(); os.fsync(stream.fileno())
    fsync_dir(output)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bank-dir",type=Path,required=True); parser.add_argument("--bank-receipt-sha256",required=True)
    parser.add_argument("--module",type=Path,required=True); parser.add_argument("--module-receipt",type=Path,required=True)
    parser.add_argument("--module-receipt-sha256",required=True)
    parser.add_argument("--repo",type=Path,required=True); parser.add_argument("--module-repo-path",required=True)
    parser.add_argument("--module-commit",required=True); parser.add_argument("--review-id",required=True); parser.add_argument("--output",type=Path,required=True)
    args=parser.parse_args(); committed=committed_bytes(args.repo,args.module_repo_path,args.module_commit)
    build(args.bank_dir,args.bank_receipt_sha256,args.module,args.module_receipt,args.module_receipt_sha256,
          args.module_commit,args.review_id,args.output,committed)
    print(f"WROTE {args.output} jobs=406")
if __name__=="__main__": main()
