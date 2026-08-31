#!/usr/bin/env python3
"""Fail-closed validation and materialization receipt for one H8 queue."""
from __future__ import annotations
import argparse, json, os, subprocess, sys, tempfile
from pathlib import Path
import generate_h8_slow_unknown_followup_queue as queues

SCHEMA="erdos85-h8-slow-unknown-followup-validation-v1"
HERE=Path(__file__).resolve().parent
VALIDATOR_SHA_FIELD="validator_sha256"

def require(ok: bool,message: str)->None:
    if not ok: raise ValueError(message)

def source_row(source_queue: dict,job: str)->dict:
    require(type(source_queue) is dict and type(source_queue.get("jobs")) is list,"malformed source queue")
    matches=[row for row in source_queue["jobs"] if type(row) is dict and row.get("id")==job]
    require(len(matches)==1,"source job is not unique in source queue")
    return matches[0]

def validate_bound_queue(queue_path: Path)->tuple[dict,Path,Path,Path]:
    queue=queues.canonical_json(queue_path,"H8 queue")
    require(queue.get("schema")==queues.SCHEMA,"unsupported H8 queue schema")
    require(queue.get("job_count")==2 and type(queue.get("jobs")) is list and len(queue["jobs"])==2,"H8 queue must contain exactly two jobs")
    for prefix in ("source_unknown_marker","source_queue","source_worker","source_spec","old_manifest","new_manifest","new_spec","parent_manifest","base","parent_cnf","lookahead"):
        path=Path(queue.get(prefix,"")); queues.canonical_file(path,prefix)
        require(queues.sha256(path)==queue.get(prefix+"_sha256") and path.stat().st_size==queue.get(prefix+"_bytes"),f"bound input mismatch: {prefix}")
    require(queue.get("probe_path")==str(queues.PROBE_PATH) and queue.get("probe_sha256")==queues.PROBE_SHA256 and queues.sha256(queues.PROBE_PATH)==queues.PROBE_SHA256,"probe identity mismatch")
    require(queue.get("materializer_path")==str(queues.MATERIALIZER_PATH) and queue.get("materializer_sha256")==queues.MATERIALIZER_SHA256 and queues.sha256(queues.MATERIALIZER_PATH)==queues.MATERIALIZER_SHA256,"materializer identity mismatch")
    require(queue.get("generator_path")==str(queues.GENERATOR_PATH) and queue.get("generator_sha256")==queues.sha256(queues.GENERATOR_PATH),"generator identity mismatch")
    require(queue.get("validator_path")==str(Path(__file__).resolve()) and queue.get("validator_sha256")==queues.sha256(Path(__file__).resolve()),"validator identity mismatch")
    source=queues.canonical_json(Path(queue["source_queue"]),"source queue")
    row=source_row(source,queue.get("source_job"))
    require(row.get("manifest")==queue["old_manifest"] and row.get("manifest_sha256")==queue["old_manifest_sha256"],"source row/old manifest mismatch")
    expected=queues.build_queue(job=queue["source_job"],marker=Path(queue["source_unknown_marker"]),old_manifest=Path(queue["old_manifest"]),new_manifest=Path(queue["new_manifest"]),new_spec=Path(queue["new_spec"]),source_queue=Path(queue["source_queue"]),source_worker=Path(queue["source_worker"]),parent_manifest=Path(queue["parent_manifest"]),base=Path(queue["base"]),parent_cnf=Path(queue["parent_cnf"]),lookahead=Path(queue["lookahead"]),cadical_sha=queue.get("cadical_sha256",""),cap=queue.get("cap_s"))
    require(queue==expected,"queue differs from authenticated reconstruction")
    return queue,Path(queue["new_manifest"]),Path(queue["new_spec"]),Path(queue["old_manifest"])

def materialize_and_check(queue: dict,new_manifest: Path,new_spec: Path,runner=subprocess.run)->tuple[dict,list[dict]]:
    results=[]
    with tempfile.TemporaryDirectory(prefix="erdos85-h8-validate.") as raw:
        root=Path(raw)
        parent_output=root/"parent.cnf"
        parent_command=[sys.executable,str(queues.MATERIALIZER_PATH),"materialize","--manifest",queue["old_manifest"],"--parent-manifest",queue["parent_manifest"],"--tree-spec",queue["source_spec"],"--base",queue["base"],"--leaf",queue["source_job"],"--output",str(parent_output)]
        parent_run=runner(parent_command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
        require(parent_run.returncode==0 and parent_output.is_file(),f"parent materialization failed: {parent_run.stdout.strip()}")
        require(parent_output.read_bytes()==Path(queue["parent_cnf"]).read_bytes(),"parent CNF differs from deterministic materialization")
        parent_result={"id":queue["source_job"],"cnf_sha256":queues.sha256(parent_output),"cnf_bytes":parent_output.stat().st_size}
        for job in queue["jobs"]:
            output=root/f"{job['id']}.cnf"
            command=[sys.executable,str(queues.MATERIALIZER_PATH),"materialize","--manifest",str(new_manifest),"--parent-manifest",queue["parent_manifest"],"--tree-spec",str(new_spec),"--base",queue["base"],"--leaf",job["id"],"--output",str(output)]
            run=runner(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
            require(run.returncode==0 and output.is_file(),f"materialization failed for {job['id']}: {run.stdout.strip()}")
            with output.open("rb") as stream: header=stream.readline().decode("ascii").strip()
            clauses=queue["base_clauses"]+len(job["units"])
            require(header==f"p cnf {queue['variables']} {clauses}",f"unexpected child CNF shape: {job['id']}")
            results.append({"id":job["id"],"path":job["path"],"cnf_sha256":queues.sha256(output),"cnf_bytes":output.stat().st_size,"variables":queue["variables"],"clauses":clauses})
    return parent_result,results

def validate_and_receipt(queue_path: Path,receipt_path: Path,runner=subprocess.run,before_output=None)->dict:
    queue_pin=queues.file_pin(queue_path,"H8 queue")
    pre_queue=queues.canonical_json(queue_path,"H8 queue pre-read")
    prefixes=("source_unknown_marker","source_queue","source_worker","source_spec","old_manifest","new_manifest","new_spec","parent_manifest","base","parent_cnf","lookahead")
    require(all(isinstance(pre_queue.get(prefix),str) for prefix in prefixes),"H8 queue input paths missing")
    paths=[(Path(pre_queue[prefix]),prefix) for prefix in prefixes]+[(queues.GENERATOR_PATH,"generator"),(Path(__file__).resolve(),"validator"),(queues.PROBE_PATH,"probe"),(queues.MATERIALIZER_PATH,"materializer")]
    require(len({(os.stat(path).st_dev,os.stat(path).st_ino) for path,_ in paths})==len(paths),"validation inputs alias")
    pins=[(path,queues.file_pin(path,label),label) for path,label in paths]
    queue,new_manifest,new_spec,_=validate_bound_queue(queue_path)
    parent,children=materialize_and_check(queue,new_manifest,new_spec,runner)
    queues.require_pin(queue_path,queue_pin,"H8 queue")
    for path,pin,label in pins: queues.require_pin(path,pin,label)
    if before_output is not None: before_output()
    queues.require_pin(queue_path,queue_pin,"H8 queue")
    for path,pin,label in pins: queues.require_pin(path,pin,label)
    receipt={"schema":SCHEMA,"status":"PASS","queue":str(queue_path),"queue_sha256":queue_pin[0],"queue_bytes":queue_pin[1],"generator_path":queue["generator_path"],"generator_sha256":queue["generator_sha256"],"validator_path":str(Path(__file__).resolve()),VALIDATOR_SHA_FIELD:queues.sha256(Path(__file__).resolve()),"probe_sha256":queues.PROBE_SHA256,"materializer_sha256":queues.MATERIALIZER_SHA256,"source_job":queue["source_job"],"parent":parent,"split_variable":queue["split_variable"],"job_count":2,"children":children}
    queues.create_only_json(receipt_path,receipt); return receipt

def main()->None:
    parser=argparse.ArgumentParser(description=__doc__); parser.add_argument("--queue",type=Path,required=True); parser.add_argument("--receipt",type=Path,required=True); a=parser.parse_args()
    queue=a.queue.resolve()
    result=validate_and_receipt(queue,a.receipt.absolute()); print(f"H8 FOLLOWUP QUEUE VERIFIED jobs=2 receipt_sha256={queues.sha256(a.receipt.absolute())}")

if __name__=="__main__": main()
