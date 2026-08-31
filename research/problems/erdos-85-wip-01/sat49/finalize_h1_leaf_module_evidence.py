#!/usr/bin/env python3
"""Bind the reviewed H1 payload bank to one committed generated Lean tree."""

from __future__ import annotations

import argparse, csv, hashlib, importlib.util, io, json, os, re, subprocess, tempfile
from pathlib import Path, PurePosixPath

SHA256=re.compile(r"[0-9a-f]{64}")
COMMIT=re.compile(r"[0-9a-f]{40}")
TAG=re.compile(r"[0-9a-f]{16}")
REVIEW=re.compile(r"[0-9]+")
SORRY=re.compile(r"(?<![A-Za-z0-9_'])(?:sorry|admit)(?![A-Za-z0-9_'])")
PROFILE_NAMES=("BBBB","ABBB","AABB","AAAB","AAAA")
BANK_SCHEMA="erdos85-h1-capacity-payload-bank-v1"
PAYLOAD_SCHEMA="erdos85-h1-capacity-payload-index-v1"
AUDIT_SCHEMA="erdos85-h1-capacity-replay-audit-v1"
REPLAY_SCHEMA="erdos85-h1-capacity-replay-evidence-v1"
REINDEX_SCHEMA="erdos85-h1-v2-capacity-reindex-v1"
LEAF_SCHEMA="erdos85-h1-leaf-module-index-v1"
LAYOUT_SCHEMA="erdos85-h1-v2-aggregate-layout-v1"
ADAPTER_SCHEMA="erdos85-h1-post-aggregate-adapter-generation-v1"
EVIDENCE_SCHEMA="erdos85-h1-committed-leaf-evidence-v1"
RECEIPT_SCHEMA="erdos85-h1-leaf-module-evidence-receipt-v1"

def canonical(value):
    return (json.dumps(value,ensure_ascii=True,allow_nan=False,sort_keys=True,
                       separators=(",",":"))+"\n").encode("ascii")

def sha(path):
    digest=hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda:stream.read(1<<20),b""): digest.update(block)
    return digest.hexdigest()

def require_path(path,label,kind="file"):
    if not path.is_absolute() or path!=path.resolve() or path.is_symlink():
        raise ValueError(f"{label} is not an absolute canonical non-symlink path")
    if kind=="file" and not path.is_file(): raise ValueError(f"{label} is not a file")
    if kind=="dir" and not path.is_dir(): raise ValueError(f"{label} is not a directory")

def require_ancestry(root,path,label):
    require_path(root,"repo","dir")
    try: parts=path.relative_to(root).parts
    except ValueError as error: raise ValueError(f"{label} escapes repo") from error
    current=root
    for part in parts:
        current/=part
        if current.is_symlink(): raise ValueError(f"{label} traverses a symlink")

def require_file(path,pin,label):
    require_path(path,label)
    if not isinstance(pin,str) or SHA256.fullmatch(pin) is None or sha(path)!=pin:
        raise ValueError(f"{label} hash mismatch")

def read_json(path,pin,label,pretty=False):
    require_file(path,pin,label); raw=path.read_bytes()
    try: value=json.loads(raw)
    except (UnicodeDecodeError,json.JSONDecodeError) as error: raise ValueError(f"{label} JSON malformed") from error
    expected=(json.dumps(value,indent=2,sort_keys=True)+"\n").encode() if pretty else canonical(value)
    if not isinstance(value,dict) or raw!=expected: raise ValueError(f"{label} serialization mismatch")
    return value

def relative(repo,path,label):
    require_ancestry(repo,path,label)
    return path.relative_to(repo).as_posix()

def nested(root,text,label):
    if not isinstance(text,str) or not text or "\\" in text:
        raise ValueError(f"{label} is not a canonical relative POSIX path")
    pure=PurePosixPath(text)
    if pure.is_absolute() or pure.as_posix()!=text or any(part in (".","..","") for part in pure.parts):
        raise ValueError(f"{label} is not a canonical relative POSIX path")
    require_path(root,"bank root","dir")
    path=root.joinpath(*pure.parts)
    require_ancestry(root,path,label)
    return path

def file_identity(path):
    return {"bytes":path.stat().st_size,"path":str(path),"sha256":sha(path)}

def read_capacity_index(path,pin,profile_counts):
    require_file(path,pin,"capacity index")
    columns=("orbit","profile","localIndex","compact_lrat_sha256","raw_lrat_sha256","cnf_sha256",
      "lrat_actions","source_cnf_clauses","compact_bytes","stub_ready","binary_lrat_sha256",
      "binary_bytes","lz4_frame_sha256","lz4_frame_bytes","packed_lz4_sha256","packed_lz4_bytes")
    rows=[]
    with path.open(newline="") as stream:
        reader=csv.DictReader(stream,delimiter="\t")
        if tuple(reader.fieldnames or ())!=columns: raise ValueError("capacity index header mismatch")
        for raw in reader:
            try: profile=PROFILE_NAMES.index(raw["profile"]); local=int(raw["localIndex"])
            except ValueError as error: raise ValueError("capacity index coordinate malformed") from error
            hashes=[raw[key] for key in columns if key.endswith("sha256")]
            if (TAG.fullmatch(raw["orbit"]) is None or any(SHA256.fullmatch(item) is None for item in hashes)
                    or raw["stub_ready"]!="1"):
                raise ValueError("capacity index row malformed/not ready")
            rows.append({"tag":raw["orbit"],"profile":profile,"local_index":local,
                         "compact_sha256":raw["compact_lrat_sha256"],
                         "raw_sha256":raw["raw_lrat_sha256"],"cnf_sha256":raw["cnf_sha256"],
                         "packed_sha256":raw["packed_lz4_sha256"],
                         "packed_bytes":int(raw["packed_lz4_bytes"])})
    expected=[(p,i) for p,count in enumerate(profile_counts) for i in range(count)]
    if [(row["profile"],row["local_index"]) for row in rows]!=expected or len({r["tag"] for r in rows})!=len(rows):
        raise ValueError("capacity index is not the exact ordered capacity bijection")
    return rows

def git_root(repo):
    result=subprocess.run(["git","rev-parse","--show-toplevel"],cwd=repo,check=True,
                          stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
    if Path(result.stdout.strip())!=repo: raise ValueError("repo is not canonical Git root")

def git_batch(repo,commit,repo_paths):
    """Read the commit and every blob using exactly one authenticated batch stream."""
    specs=[commit,*[f"{commit}:{path}" for path in repo_paths]]
    process=subprocess.run(["git","cat-file","--batch"],cwd=repo,
                           input=("\n".join(specs)+"\n").encode("ascii"),
                           stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    stream=io.BytesIO(process.stdout)
    results=[]
    try:
        for spec in specs:
            header=stream.readline()
            fields=header.rstrip(b"\n").split()
            if len(fields)!=3 or fields[1] not in (b"commit",b"blob"):
                raise ValueError(f"Git object missing/malformed: {spec}")
            try: size=int(fields[2])
            except ValueError as error: raise ValueError("Git batch size malformed") from error
            body=stream.read(size)
            if len(body)!=size or stream.read(1)!=b"\n": raise ValueError("Git batch body truncated")
            results.append({"oid":fields[0].decode("ascii"),"type":fields[1].decode("ascii"),"bytes":body})
    finally: stream.close()
    if process.returncode!=0 or process.stderr or results[0]["type"]!="commit" or results[0]["oid"]!=commit \
            or any(item["type"]!="blob" for item in results[1:]):
        raise ValueError("Git batch authentication failed")
    return results[0],dict(zip(repo_paths,results[1:],strict=True))

def exact_fields(value,fields,label):
    if not isinstance(value,dict) or set(value)!=set(fields): raise ValueError(f"{label} schema mismatch")

def validate(repo,reviewed_commit,review_id,bank_receipt,bank_pin,reindex_receipt,reindex_pin,
             layout_path,layout_pin,adapter_receipt,adapter_pin,leaf_index_path,leaf_pin,
             profile_counts):
    require_path(repo,"repo","dir"); git_root(repo)
    if COMMIT.fullmatch(reviewed_commit) is None or REVIEW.fullmatch(review_id) is None:
        raise ValueError("full reviewed commit/review id malformed")
    total=sum(profile_counts)
    bank=read_json(bank_receipt,bank_pin,"payload bank receipt")
    bank_fields={"all_even_manifest_path","all_even_manifest_sha256","capacity_inventory_path",
      "capacity_inventory_sha256","compact_universe_path","compact_universe_sha256",
      "complement_manifest_path","complement_manifest_sha256","coverage_receipt_path",
      "coverage_receipt_sha256","coverage_terminal_counts","leaf_count","ledger_snapshot_path",
      "ledger_snapshot_sha256","materializer_sha256","materializer_source","payload_identity_sha256",
      "payload_index_path","payload_index_sha256","profile_counts","replay_audit_path",
      "replay_audit_sha256","s3_bucket","s3_prefix","schema","selected_ledger_identity_sha256",
      "source_index_path","source_index_sha256","toolchain_path","toolchain_sha256"}
    exact_fields(bank,bank_fields,"payload bank receipt")
    if bank["schema"]!=BANK_SCHEMA or bank["leaf_count"]!=total or bank["profile_counts"]!=list(profile_counts):
        raise ValueError("payload bank receipt contract mismatch")
    bank_root=bank_receipt.parent
    payload_path=Path(bank["payload_index_path"]); audit_path=Path(bank["replay_audit_path"])
    if payload_path!=bank_root/"payload-index.json" or audit_path!=bank_root/"replay-audit.json":
        raise ValueError("payload bank nested path mismatch")
    payload=read_json(payload_path,bank["payload_index_sha256"],"payload index")
    audit=read_json(audit_path,bank["replay_audit_sha256"],"replay audit")
    exact_fields(payload,{"capacity_inventory_sha256","profile_counts","rows","schema"},"payload index")
    exact_fields(audit,{"capacity_inventory_sha256","coverage_receipt_sha256","profile_counts","rows",
                        "replay_evidence_identity_sha256","schema"},"replay audit")
    if (payload["schema"]!=PAYLOAD_SCHEMA or audit["schema"]!=AUDIT_SCHEMA
            or payload["capacity_inventory_sha256"]!=bank["capacity_inventory_sha256"]
            or audit["capacity_inventory_sha256"]!=bank["capacity_inventory_sha256"]
            or audit["coverage_receipt_sha256"]!=bank["coverage_receipt_sha256"]
            or payload["profile_counts"]!=list(profile_counts) or audit["profile_counts"]!=list(profile_counts)
            or len(payload["rows"])!=total or len(audit["rows"])!=total
            or hashlib.sha256(canonical(audit["rows"])).hexdigest()!=audit["replay_evidence_identity_sha256"]):
        raise ValueError("payload/replay audit crosslink mismatch")
    payload_fields={"binary_bytes","binary_lrat_sha256","capacity_local_index","cnf_sha256",
      "compact_bytes","compact_lrat_sha256","gzip_bytes","gzip_sha256","ledger_namespace",
      "ledger_path","ledger_sha256","lrat_actions","lz4_frame_bytes","lz4_frame_sha256",
      "packed_lz4_bytes","packed_lz4_path","packed_lz4_sha256","profile","raw_lrat_bytes",
      "raw_lrat_sha256","s3_key","source_cnf_clauses","tag"}
    audit_fields={"ledger_namespace","ledger_sha256","packed_lz4_sha256","replay_evidence_path",
                  "replay_evidence_sha256","replay_command_identity_sha256","s3_key","tag"}
    if any(not isinstance(row,dict) or set(row)!=payload_fields for row in payload["rows"]):
        raise ValueError("payload row schema mismatch")
    if any(not isinstance(row,dict) or set(row)!=audit_fields for row in audit["rows"]):
        raise ValueError("replay audit row schema mismatch")
    expected_payload_identity=hashlib.sha256(canonical([{"path":row["packed_lz4_path"],
      "sha256":row["packed_lz4_sha256"],"bytes":row["packed_lz4_bytes"]} for row in payload["rows"]])).hexdigest()
    if expected_payload_identity!=bank["payload_identity_sha256"]:
        raise ValueError("payload identity mismatch")
    reindex=read_json(reindex_receipt,reindex_pin,"reindex receipt",pretty=True)
    reindex_fields={"capacity_total","dropped_outside_capacity_tags","emitted_rows","indexes","inventory",
                    "inventory_sha256","output","output_sha256","require_complete","schema"}
    exact_fields(reindex,reindex_fields,"reindex receipt")
    index_path=Path(reindex["output"])
    if (reindex["schema"]!=REINDEX_SCHEMA or reindex["capacity_total"]!=total
            or reindex["emitted_rows"]!=total or reindex["dropped_outside_capacity_tags"]!=[]
            or reindex["require_complete"] is not True or reindex["inventory"]!=bank["capacity_inventory_path"]
            or reindex["inventory_sha256"]!=bank["capacity_inventory_sha256"]):
        raise ValueError("reindex/bank mismatch")
    inventory_path=Path(reindex["inventory"]); require_file(inventory_path,reindex["inventory_sha256"],"capacity inventory")
    source_indexes=reindex["indexes"]
    if (not isinstance(source_indexes,list) or not source_indexes
            or any(not isinstance(item,dict) or set(item)!={"path","sha256"} for item in source_indexes)):
        raise ValueError("reindex source index schema mismatch")
    source_index_paths=[]
    for item in source_indexes:
        path=Path(item["path"]); require_file(path,item["sha256"],"reindex source index"); source_index_paths.append(path)
    rows=read_capacity_index(index_path,reindex["output_sha256"],profile_counts)
    leaf=read_json(leaf_index_path,leaf_pin,"leaf module index")
    exact_fields(leaf,{"capacity_index_sha256","leaf_count","modules","schema"},"leaf module index")
    if leaf["schema"]!=LEAF_SCHEMA or leaf["capacity_index_sha256"]!=reindex["output_sha256"] \
            or leaf["leaf_count"]!=total or len(leaf["modules"])!=total:
        raise ValueError("leaf module index mismatch")
    layout=read_json(layout_path,layout_pin,"aggregate layout",pretty=True)
    layout_fields={"bank_size","inputs","inventory_contract","leaf_count","leaf_members_sha256","modules",
                   "prefixes","profile_bank_counts","schema","top_module"}
    exact_fields(layout,layout_fields,"aggregate layout")
    if layout["schema"]!=LAYOUT_SCHEMA or layout["leaf_count"]!=total \
            or layout.get("inputs",{}).get("index")!=file_identity(index_path):
        raise ValueError("aggregate layout/index mismatch")
    module_fields={"direct_import_count","direct_imports","file","kind","members","module",
                   "source_bytes","source_sha256","theorem"}
    if (not isinstance(layout["modules"],list) or not layout["modules"]
            or any(not isinstance(record,dict) or set(record)!=module_fields for record in layout["modules"])):
        raise ValueError("aggregate layout module schema mismatch")
    adapter=read_json(adapter_receipt,adapter_pin,"adapter receipt")
    adapter_required={"aggregate_layout_path","aggregate_layout_sha256","aggregate_source_root",
      "aggregate_sources_identity_sha256","capacity_index_path","capacity_index_sha256",
      "capacity_reindex_receipt_path","capacity_reindex_receipt_sha256","generator_sha256","generator_source",
      "input_top_module","input_top_path","input_top_repo_path","input_top_sha256","input_top_theorem",
      "leaf_count","leaf_module_index_path","leaf_module_index_sha256","output_bytes","output_path",
      "output_sha256","output_source_module","output_theorem","repo","schema"}
    exact_fields(adapter,adapter_required,"adapter receipt")
    if (adapter["schema"]!=ADAPTER_SCHEMA or adapter["repo"]!=str(repo) or adapter["leaf_count"]!=total
            or adapter["aggregate_layout_path"]!=str(layout_path) or adapter["aggregate_layout_sha256"]!=layout_pin
            or adapter["capacity_index_path"]!=str(index_path) or adapter["capacity_index_sha256"]!=reindex["output_sha256"]
            or adapter["capacity_reindex_receipt_path"]!=str(reindex_receipt)
            or adapter["capacity_reindex_receipt_sha256"]!=reindex_pin
            or adapter["leaf_module_index_path"]!=str(leaf_index_path)
            or adapter["leaf_module_index_sha256"]!=leaf_pin):
        raise ValueError("adapter receipt crosslink mismatch")
    generator_path=repo/adapter["generator_source"]
    require_file(generator_path,adapter["generator_sha256"],"adapter generator")
    if tuple(profile_counts)==(1485,3617,4717,2693,839):
        adapter_source=repo/adapter["generator_source"]
        spec=importlib.util.spec_from_file_location("h1_committed_adapter_validator",adapter_source)
        module=importlib.util.module_from_spec(spec); assert spec.loader is not None; spec.loader.exec_module(module)
        _,validated_core,_=module.validate(repo,layout_path,layout_pin,Path(adapter["aggregate_source_root"]),
          index_path,reindex["output_sha256"],reindex_receipt,reindex_pin,leaf_index_path,leaf_pin)
        for key,value in validated_core.items():
            if adapter.get(key)!=value: raise ValueError(f"adapter receipt recomputation mismatch: {key}")
    source_records=[]; source_paths=[]; nested_pins={}
    leaf_fields={"local_index","orbit","packed_lrat_sha256","profile","source_bytes","source_module",
                 "source_path","source_sha256"}
    evidence_rows=[]
    for index,(row,payload_row,audit_row,module) in enumerate(zip(rows,payload["rows"],audit["rows"],leaf["modules"],strict=True)):
        exact_fields(module,leaf_fields,"leaf module row")
        coordinate=(row["tag"],row["profile"],row["local_index"],row["packed_sha256"])
        if ((payload_row.get("tag"),payload_row.get("profile"),payload_row.get("capacity_local_index"),
             payload_row.get("packed_lz4_sha256"))!=coordinate
                or (audit_row.get("tag"),audit_row.get("packed_lz4_sha256"))!=(row["tag"],row["packed_sha256"])
                or (module["orbit"],module["profile"],module["local_index"],module["packed_lrat_sha256"])!=coordinate):
            raise ValueError(f"leaf {index}: ordered bank/module crosslink mismatch")
        packed=nested(bank_root,payload_row["packed_lz4_path"],"packed payload path")
        ledger=nested(bank_root,payload_row["ledger_path"],"selected ledger path")
        replay=nested(bank_root,audit_row["replay_evidence_path"],"replay evidence path")
        require_file(packed,row["packed_sha256"],f"{row['tag']} packed payload")
        if packed.stat().st_size!=row["packed_bytes"]: raise ValueError("packed byte mismatch")
        require_file(ledger,payload_row["ledger_sha256"],f"{row['tag']} selected ledger")
        require_file(replay,audit_row["replay_evidence_sha256"],f"{row['tag']} replay evidence")
        nested_pins.update({str(packed):row["packed_sha256"],str(ledger):payload_row["ledger_sha256"],
                            str(replay):audit_row["replay_evidence_sha256"]})
        replay_value=read_json(replay,audit_row["replay_evidence_sha256"],"leaf replay evidence")
        replay_fields={"accepted_marker","commands","cnf_sha256","compact_bytes","compact_lrat_sha256",
                       "image","lratreplay_sha256","schema","table_path","table_sha256","tag"}
        exact_fields(replay_value,replay_fields,"leaf replay evidence")
        command_fields={"argv","command_identity_sha256","cumulative_children_maxrss_kb","cwd",
          "environment","kind","rc","stderr_bytes","stderr_path","stderr_sha256","stdout_bytes",
          "stdout_path","stdout_sha256","system_ns","user_ns","wall_ns"}
        commands=replay_value["commands"]
        expected_commands={"cnf_check","cnf_emit","compress","decode","encode","fetch","replay",
                           "replay_pin","v2cnf_pin"}
        if (replay_value["schema"]!=REPLAY_SCHEMA or replay_value["tag"]!=row["tag"]
                or replay_value["cnf_sha256"]!=row["cnf_sha256"]
                or replay_value["compact_lrat_sha256"]!=row["compact_sha256"]
                or replay_value["accepted_marker"]!="LRAT accepted: true"
                or not isinstance(commands,dict) or set(commands)!=expected_commands
                or any(not isinstance(record,dict) or set(record)!=command_fields or record["kind"]!=kind
                       for kind,record in commands.items())
                or commands["replay"]["command_identity_sha256"]!=audit_row["replay_command_identity_sha256"]
                or audit_row["ledger_namespace"]!=payload_row["ledger_namespace"]
                or audit_row["ledger_sha256"]!=payload_row["ledger_sha256"]
                or audit_row["s3_key"]!=payload_row["s3_key"]):
            raise ValueError("leaf replay evidence crosslink mismatch")
        table=nested(bank_root,replay_value["table_path"],"retained v2cnf table path")
        require_file(table,replay_value["table_sha256"],f"{row['tag']} retained v2cnf table")
        nested_pins[str(table)]=replay_value["table_sha256"]
        for kind,record in commands.items():
            for stream_name in ("stdout","stderr"):
                retained=record[f"{stream_name}_path"]
                if retained is None:
                    if (kind,stream_name) not in {("cnf_emit","stdout"),("decode","stdout")}:
                        raise ValueError("unexpected unretained command stream")
                    continue
                log=nested(bank_root,retained,f"{kind} {stream_name} path")
                require_file(log,record[f"{stream_name}_sha256"],f"{row['tag']} {kind} {stream_name}")
                if log.stat().st_size!=record[f"{stream_name}_bytes"]:
                    raise ValueError("retained command log byte mismatch")
                nested_pins[str(log)]=record[f"{stream_name}_sha256"]
        source=Path(module["source_path"]); repo_path=relative(repo,source,"leaf source")
        require_file(source,module["source_sha256"],"leaf source")
        if source.stat().st_size!=module["source_bytes"]: raise ValueError("leaf source byte mismatch")
        source_paths.append(repo_path); source_records.append((source,module))
        evidence_rows.append({"capacity_local_index":row["local_index"],"ledger_path":payload_row["ledger_path"],
          "ledger_sha256":payload_row["ledger_sha256"],"leaf_repo_path":repo_path,
          "packed_path":payload_row["packed_lz4_path"],"packed_sha256":row["packed_sha256"],
          "profile":row["profile"],"replay_evidence_path":audit_row["replay_evidence_path"],
          "replay_evidence_sha256":audit_row["replay_evidence_sha256"],"tag":row["tag"]})
    layout_repo_path=relative(repo,layout_path,"aggregate layout")
    source_paths.append(layout_repo_path)
    aggregate_records=[]
    aggregate_worktree_identities=[]
    for record in layout["modules"]:
        path=repo/"proofs"/Path(*record["module"].split(".")).with_suffix(".lean")
        repo_path=relative(repo,path,"aggregate source"); require_file(path,record["source_sha256"],"aggregate source")
        if path.stat().st_size!=record["source_bytes"]: raise ValueError("aggregate source bytes mismatch")
        source_paths.append(repo_path); aggregate_records.append((path,record))
        aggregate_worktree_identities.append({"repo_path":repo_path,"bytes":path.stat().st_size,"sha256":sha(path)})
    if hashlib.sha256(canonical(aggregate_worktree_identities)).hexdigest()!=adapter["aggregate_sources_identity_sha256"]:
        raise ValueError("adapter aggregate tree identity mismatch")
    adapter_path=Path(adapter["output_path"]); adapter_repo_path=relative(repo,adapter_path,"adapter source")
    require_file(adapter_path,adapter["output_sha256"],"adapter source")
    if adapter_path.stat().st_size!=adapter["output_bytes"]: raise ValueError("adapter source bytes mismatch")
    source_paths.append(adapter_repo_path)
    if len(source_paths)!=len(set(source_paths)): raise ValueError("generated source path collision")
    commit_object,blobs=git_batch(repo,reviewed_commit,source_paths)
    identities=[]
    for repo_path in source_paths:
        path=repo/repo_path; blob=blobs[repo_path]
        if blob["bytes"]!=path.read_bytes(): raise ValueError(f"committed blob/worktree mismatch: {repo_path}")
        if SORRY.search(blob["bytes"].decode("utf-8")): raise ValueError(f"sorry/admit in committed source: {repo_path}")
        identities.append({"blob_oid":blob["oid"],"bytes":len(blob["bytes"]),"repo_path":repo_path,
                           "sha256":hashlib.sha256(blob["bytes"]).hexdigest()})
    identity_by_path={item["repo_path"]:item for item in identities}
    for row in evidence_rows:
        leaf_identity=identity_by_path[row["leaf_repo_path"]]
        row.update({"leaf_blob_oid":leaf_identity["blob_oid"],"leaf_source_bytes":leaf_identity["bytes"],
                    "leaf_source_sha256":leaf_identity["sha256"]})
    aggregate_paths={layout_repo_path,*[relative(repo,path,"aggregate source") for path,_ in aggregate_records]}
    leaf_paths_set={row["leaf_repo_path"] for row in evidence_rows}
    leaf_identity=hashlib.sha256(canonical([identity_by_path[path] for path in source_paths if path in leaf_paths_set])).hexdigest()
    aggregate_identity=hashlib.sha256(canonical([identity_by_path[path] for path in source_paths if path in aggregate_paths])).hexdigest()
    generated_identity=hashlib.sha256(canonical(identities)).hexdigest()
    evidence={"aggregate_layout_source_identity":identity_by_path[layout_repo_path],
      "aggregate_tree_identity_sha256":aggregate_identity,"adapter_repo_path":adapter_repo_path,
      "adapter_source_identity":identity_by_path[adapter_repo_path],"generated_tree_identity_sha256":generated_identity,
      "leaf_count":total,"leaf_tree_identity_sha256":leaf_identity,"profile_counts":list(profile_counts),
      "review_id":review_id,"reviewed_commit":reviewed_commit,"rows":evidence_rows,"schema":EVIDENCE_SCHEMA}
    source_index=Path(bank["source_index_path"]); toolchain=Path(bank["toolchain_path"])
    require_file(source_index,bank["source_index_sha256"],"bank source index")
    require_file(toolchain,bank["toolchain_sha256"],"bank toolchain")
    pins={str(bank_receipt):bank_pin,str(payload_path):bank["payload_index_sha256"],
      str(audit_path):bank["replay_audit_sha256"],str(source_index):bank["source_index_sha256"],
      str(toolchain):bank["toolchain_sha256"],str(reindex_receipt):reindex_pin,
      str(index_path):reindex["output_sha256"],str(inventory_path):reindex["inventory_sha256"],
      str(layout_path):layout_pin,str(adapter_receipt):adapter_pin,str(generator_path):adapter["generator_sha256"],
      str(leaf_index_path):leaf_pin,**nested_pins}
    pins.update({str(path):item["sha256"] for path,item in
                 ((Path(source["path"]),source) for source in source_indexes)})
    pins.update({str(repo/path):identity_by_path[path]["sha256"] for path in source_paths})
    receipt_core={"adapter_receipt_path":str(adapter_receipt),"adapter_receipt_sha256":adapter_pin,
      "aggregate_layout_path":str(layout_path),"aggregate_layout_sha256":layout_pin,
      "bank_receipt_path":str(bank_receipt),"bank_receipt_sha256":bank_pin,
      "capacity_reindex_receipt_path":str(reindex_receipt),"capacity_reindex_receipt_sha256":reindex_pin,
      "commit_object_oid":commit_object["oid"],"generated_tree_identity_sha256":generated_identity,
      "endpoint_module":adapter["output_source_module"],"endpoint_source_path":adapter_repo_path,
      "endpoint_source_sha256":identity_by_path[adapter_repo_path]["sha256"],
      "endpoint_theorem":adapter["output_theorem"],
      "leaf_count":total,"leaf_module_index_path":str(leaf_index_path),"leaf_module_index_sha256":leaf_pin,
      "profile_counts":list(profile_counts),"repo":str(repo),"review_id":review_id,
      "reviewed_commit":reviewed_commit}
    return evidence,receipt_core,pins

def publish(output,evidence,receipt_core,pins):
    require_path(output.parent,"output parent","dir")
    if not output.is_absolute() or output!=output.resolve(strict=False) or output.exists() or output.is_symlink():
        raise ValueError("output must be an absent canonical directory")
    producer=Path(__file__).resolve(); pins={**pins,str(producer):sha(producer)}
    with tempfile.TemporaryDirectory(prefix=".h1-committed-evidence-",dir=output.parent) as raw:
        stage=Path(raw); publication=stage/"publication"; publication.mkdir()
        evidence_raw=canonical(evidence); evidence_path=publication/"leaf-evidence.json"
        with evidence_path.open("xb") as stream: stream.write(evidence_raw); stream.flush(); os.fsync(stream.fileno())
        for path,pin in pins.items(): require_file(Path(path),pin,"input drift before receipt")
        receipt={**receipt_core,"evidence_path":"leaf-evidence.json",
          "evidence_sha256":hashlib.sha256(evidence_raw).hexdigest(),"producer_path":str(producer),
          "producer_sha256":pins[str(producer)],"schema":RECEIPT_SCHEMA}
        receipt_raw=canonical(receipt); receipt_path=publication/"receipt.json"
        with receipt_path.open("xb") as stream: stream.write(receipt_raw); stream.flush(); os.fsync(stream.fileno())
        for path,pin in pins.items(): require_file(Path(path),pin,"input drift before publication")
        if evidence_path.read_bytes()!=evidence_raw or receipt_path.read_bytes()!=receipt_raw:
            raise ValueError("nested output drift")
        descriptor=os.open(publication,os.O_RDONLY)
        try: os.fsync(descriptor)
        finally: os.close(descriptor)
        if output.exists() or output.is_symlink(): raise ValueError("output appeared before publication")
        publication.rename(output)
        descriptor=os.open(output.parent,os.O_RDONLY)
        try: os.fsync(descriptor)
        finally: os.close(descriptor)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo",type=Path,required=True); parser.add_argument("--reviewed-commit",required=True)
    parser.add_argument("--review-id",required=True)
    for name in ("bank-receipt","capacity-reindex-receipt","aggregate-layout","adapter-receipt",
                 "leaf-module-index"):
        parser.add_argument(f"--{name}",type=Path,required=True); parser.add_argument(f"--{name}-sha256",required=True)
    parser.add_argument("--output",type=Path,required=True); args=parser.parse_args()
    evidence,core,pins=validate(args.repo,args.reviewed_commit,args.review_id,args.bank_receipt,
      args.bank_receipt_sha256,args.capacity_reindex_receipt,args.capacity_reindex_receipt_sha256,
      args.aggregate_layout,args.aggregate_layout_sha256,args.adapter_receipt,args.adapter_receipt_sha256,
      args.leaf_module_index,args.leaf_module_index_sha256,(1485,3617,4717,2693,839))
    publish(args.output,evidence,core,pins)
    print(f"WROTE {args.output} leaves={core['leaf_count']} commit={args.reviewed_commit}")

if __name__=="__main__": main()
