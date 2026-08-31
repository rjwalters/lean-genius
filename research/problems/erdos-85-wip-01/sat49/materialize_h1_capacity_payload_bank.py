#!/usr/bin/env python3
"""Materialize an immutable, independently replayed H1 capacity payload bank."""

from __future__ import annotations

import argparse, csv, gzip, hashlib, importlib.util, json, os, re, resource, shutil, subprocess, sys, tempfile, time
from pathlib import Path

HERE=Path(__file__).resolve().parent

def imported(name,file):
    spec=importlib.util.spec_from_file_location(name,HERE/file)
    module=importlib.util.module_from_spec(spec); assert spec.loader is not None
    spec.loader.exec_module(module); return module

FILTER=imported("h1_capacity_filter","filter_h1_capacity_inventory.py")
ENCODER=imported("h1_capacity_encoder","encode_h1_v2_binary_lrat.py")
SNAPSHOT=imported("h1_selected_ledger_snapshot","snapshot_h1_capacity_selected_ledgers.py")
SNAPSHOT_PRODUCER_SHA256="ad5b5aafe6be5575eeae1da51a7372aa889b392c23b33d411d71dc07def9a45f"
PROFILE_NAMES=("BBBB","ABBB","AABB","AAAB","AAAA")
PROFILE_COUNTS=(1485,3617,4717,2693,839)
COVERAGE_HEADER=("tag","profile","family","local_index","inventory_source","status","certified_s3",
 "host_unsat","host_cnf_sha256","host_verdict","fleet_claim","fleet_cnf_sha256","fleet_verdict",
 "cnf_sha_divergent","fleet_v2_claim","fleet_v2_cnf_sha256","fleet_v2_verdict","fleet_v3_claim",
 "fleet_v3_cnf_sha256","fleet_v3_verdict")
SOURCE_COLUMNS=("orbit","profile","localIndex","compact_lrat_sha256","raw_lrat_sha256","cnf_sha256",
 "lrat_actions","source_cnf_clauses","compact_bytes","stub_ready","binary_lrat_sha256","binary_bytes",
 "lz4_frame_sha256","lz4_frame_bytes","packed_lz4_sha256","packed_lz4_bytes")
SNAPSHOT_SCHEMA="erdos85-h1-coverage-audit-snapshot-v1"
LEDGER_SCHEMA="erdos85-h1-capacity-selected-ledgers-v1"
LEDGER_RECEIPT_SCHEMA="erdos85-h1-capacity-selected-ledgers-receipt-v1"
PAYLOAD_SCHEMA="erdos85-h1-capacity-payload-index-v1"
REPLAY_SCHEMA="erdos85-h1-capacity-replay-evidence-v1"
AUDIT_SCHEMA="erdos85-h1-capacity-replay-audit-v1"
TOOLCHAIN_SCHEMA="erdos85-h1-capacity-toolchain-v1"
BANK_SCHEMA="erdos85-h1-capacity-payload-bank-v1"
IMAGE="lean4-arm64@sha256:a5ca6c4e3328a1832d5f9b814ab7c1e35616903b3956341962a5b1a96fb6dff6"
LRATREPLAY_SHA256="37aad1d5c64a75fcb68e1ea587b2080b06c157a19c883b01d145b28b891c428c"
SHA=re.compile(r"[0-9a-f]{64}")
TIMESTAMP=re.compile(r"20[0-9]{2}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}Z")
LEDGER_KEYS=("p","i","cnf_sha256","cnf_clauses","raw_lrat_sha256","raw_lrat_bytes",
             "compact_lrat_sha256","compact_bytes","compact_gz_sha256")
HOST_KEYS={"p","i","rc","emit_s","solve_s","trim_s","cap_s","cnf_sha256","cnf_clauses",
           "drat_bytes","trim","raw_lrat_sha256","raw_lrat_bytes","compact","compact_lrat_sha256",
           "compact_bytes","compact_gz_sha256","upload"}
LEDGER_ORDER=("p","i","rc","emit_s","solve_s","trim_s","cap_s","cnf_sha256","cnf_clauses",
              "drat_bytes","trim","raw_lrat_sha256","raw_lrat_bytes","compact","compact_lrat_sha256",
              "compact_bytes","compact_gz_sha256","upload")

def canonical(value):
    return (json.dumps(value,ensure_ascii=True,allow_nan=False,sort_keys=True,separators=(",",":"))+"\n").encode("ascii")

def sha(path):
    digest=hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda:stream.read(1<<20),b""): digest.update(block)
    return digest.hexdigest()

def require_file(path,pin,label):
    if (not path.is_absolute() or path!=path.resolve() or path.is_symlink() or not path.is_file()
            or not isinstance(pin,str) or SHA.fullmatch(pin) is None or sha(path)!=pin):
        raise ValueError(f"{label} path/hash mismatch")

def read_canonical(path,pin,label):
    require_file(path,pin,label); raw=path.read_bytes(); value=json.loads(raw)
    if not isinstance(value,dict) or raw!=canonical(value): raise ValueError(f"{label} is not canonical JSON")
    return value

def recheck(pins,label):
    for raw,pin in pins.items(): require_file(Path(raw),pin,label)

def identity(path): return {"bytes":path.stat().st_size,"path":str(path),"sha256":sha(path)}

def inventory_rows(path,profile_counts):
    rows=[]; locals_=[0]*5
    for number,line in enumerate(path.read_text().splitlines(),1):
        try: profile,*values=map(int,line.split())
        except ValueError as error: raise ValueError(f"capacity inventory row {number} malformed") from error
        if profile not in range(5) or len(values)!=len(FILTER.TABLE_PAIRS) or any(v not in range(5) for v in values):
            raise ValueError(f"capacity inventory row {number} malformed")
        tag=FILTER.worker_tag(tuple(values)); rows.append({"tag":tag,"profile":profile,
            "capacity_local_index":locals_[profile],"inventory_line":line})
        locals_[profile]+=1
    if tuple(locals_)!=tuple(profile_counts) or len({row["tag"] for row in rows})!=len(rows):
        raise ValueError("capacity inventory ordering/counts mismatch")
    return rows

def terminal_coverage(receipt_path,receipt_pin,inventory_path,inventory_pin,rows,profile_counts):
    receipt=read_canonical(receipt_path,receipt_pin,"coverage receipt")
    receipt_fields={"aws","host_ledger_snapshot","inputs","live_campaign","live_named_output_paths",
        "live_named_outputs_mutated","live_outputs_after","live_outputs_before","outputs","schema","summary",
        "timestamp_utc"}
    summary=receipt.get("summary",{}); outputs=receipt.get("outputs",{}); inputs=receipt.get("inputs",{})
    total=sum(profile_counts)
    summary_fields={"anomalies","certified","cnf_sha_comparable_count","cnf_sha_divergent_count",
        "fleet_claim_tags","fleet_in_flight","fleet_ledger_rows","fleet_unknown_without_cert",
        "host_ledger_rows","pending","status_total","unknown_tags"}
    input_fields={"all_even_manifest","all_even_manifest_sha256","compact_inventory",
        "compact_inventory_sha256","complement_manifest","complement_manifest_sha256",
        "publisher","publisher_sha256","reconciler","reconciler_sha256"}
    if (set(receipt)!=receipt_fields or receipt.get("schema")!=SNAPSHOT_SCHEMA
            or set(summary)!=summary_fields or set(inputs)!=input_fields
            or receipt.get("live_named_outputs_mutated") is not False
            or summary.get("certified")!=total or summary.get("fleet_in_flight")!=0 or summary.get("pending")!=0
            or summary.get("status_total")!=total or summary.get("anomalies")!={}
            or summary.get("cnf_sha_divergent_count")!=0
            or summary.get("fleet_unknown_without_cert")!=0
            or any(value!=[] for value in summary.get("unknown_tags",{}).values())):
        raise ValueError("coverage is not an exact terminal durable audit")
    if (set(receipt["aws"])!={"bucket","profile","s3_prefix"}
            or any(not isinstance(receipt["aws"][key],str) or not receipt["aws"][key]
                   for key in receipt["aws"])
            or receipt["live_outputs_before"]!=receipt["live_outputs_after"]):
        raise ValueError("coverage audit provenance mismatch")
    input_paths=[]
    for path_key,pin_key in (("all_even_manifest","all_even_manifest_sha256"),
            ("compact_inventory","compact_inventory_sha256"),
            ("complement_manifest","complement_manifest_sha256"),("publisher","publisher_sha256"),
            ("reconciler","reconciler_sha256")):
        path=Path(inputs[path_key]); require_file(path,inputs[pin_key],f"coverage {path_key}"); input_paths.append(path)
    root=receipt_path.parent; expected_names={"counts.json","coverage.tsv","inventory_universe_diff.tsv"}
    if set(outputs)!=expected_names: raise ValueError("coverage output set mismatch")
    for name in expected_names:
        item=outputs[name]
        if set(item)!={"bytes","sha256"}: raise ValueError("coverage output identity malformed")
        require_file(root/name,item["sha256"],f"coverage {name}")
        if (root/name).stat().st_size!=item["bytes"]: raise ValueError("coverage output byte count mismatch")
    counts=json.loads((root/"counts.json").read_text())
    count_fields={"all_even_capacity","anomalies","capacity_inventory_total","capacity_only_error",
        "certified_s3_tags","cnf_sha_comparable_count","cnf_sha_divergent_count","cnf_sha_divergent_tags",
        "compact_inventory_total","compact_only_pre_capacity","fleet_claim_tags","fleet_ledger_rows",
        "fleet_unknown_without_cert","fleet_v2_claim_tags","fleet_v2_ledger_rows","fleet_v3_claim_tags",
        "fleet_v3_ledger_rows","host_ledger_rows","non_all_even_capacity","status_counts","status_total","unknown_tags"}
    unknown_fields={"certified_s3","fleet_v2_claim","fleet_v2_ledger","fleet_v3_claim",
                    "fleet_v3_ledger","host_ledger"}
    if (set(counts)!=count_fields or set(counts.get("unknown_tags",{}))!=unknown_fields
            or counts.get("capacity_inventory_total")!=total or counts.get("certified_s3_tags")!=total
            or counts.get("status_total")!=total or counts.get("status_counts")!={"certified-in-S3":total,
               "fleet-in-flight":0,"pending":0} or counts.get("anomalies")!={}
            or counts.get("capacity_only_error")!=0 or counts.get("cnf_sha_divergent_count")!=0
            or counts.get("cnf_sha_divergent_tags")!=[]
            or counts.get("fleet_unknown_without_cert")!=0
            or any(value!=[] for value in counts.get("unknown_tags",{}).values())):
        raise ValueError("coverage counts are not terminal")
    if tuple(profile_counts)==PROFILE_COUNTS and (counts.get("compact_inventory_total")!=13541
            or counts.get("compact_only_pre_capacity")!=190):
        raise ValueError("production capacity universe mismatch")
    coverage=root/"coverage.tsv"
    with coverage.open(newline="") as stream:
        reader=csv.DictReader(stream,delimiter="\t")
        if tuple(reader.fieldnames or ())!=COVERAGE_HEADER: raise ValueError("coverage header mismatch")
        coverage_rows=list(reader)
    by_tag={row["tag"]:row for row in coverage_rows}
    if (len(by_tag)!=len(coverage_rows) or set(by_tag)!={row["tag"] for row in rows}
            or any(row["status"]!="certified-in-S3" or row["certified_s3"]!="1"
                   or row["cnf_sha_divergent"]!="0" for row in coverage_rows)):
        raise ValueError("coverage is not terminal in capacity order")
    return receipt,[by_tag[row["tag"]] for row in rows],[receipt_path,root/"counts.json",coverage,
        root/"inventory_universe_diff.tsv",*input_paths]

def parse_ledger(path,pin,tag,namespace):
    require_file(path,pin,f"{namespace} ledger")
    raw=path.read_bytes()
    if raw.count(b"\n")!=1 or not raw.endswith(b"\n"): raise ValueError("ledger is not one canonical line")
    fields=raw[:-1].decode("ascii").split()
    pairs=[token.split("=",1) for token in fields if "=" in token]
    if len({key for key,_ in pairs})!=len(pairs): raise ValueError(f"{tag}: duplicate ledger key")
    values=dict(pairs)
    expected_keys=HOST_KEYS | ({"node"} if namespace in ("v2","v3") else set())
    if (len(fields)!=3+len(expected_keys) or TIMESTAMP.fullmatch(fields[0]) is None
            or fields[1]!=tag or fields[2]!=f"p={values.get('p')}" or fields[3]!=f"i={values.get('i')}"
            or fields[4]!="UNSAT" or fields.count("UNSAT")!=1 or set(values)!=expected_keys
            or [key for key,_ in pairs]!=list(LEDGER_ORDER)+(["node"] if namespace in ("v2","v3") else [])
            or values.get("rc")!="20"
            or values.get("upload")!="uploaded" or values.get("compact")!="ok"
            or values.get("trim")!="VERIFIED" or set(LEDGER_KEYS)-set(values)):
        raise ValueError(f"{tag}: {namespace} ledger malformed")
    result={"profile":values["p"],"source_local_index":values["i"],
        "cnf_sha256":values["cnf_sha256"],"cnf_clauses":values["cnf_clauses"],
        "raw_lrat_sha256":values["raw_lrat_sha256"],"raw_lrat_bytes":values["raw_lrat_bytes"],
        "compact_lrat_sha256":values["compact_lrat_sha256"],"compact_lrat_bytes":values["compact_bytes"],
        "gzip_sha256":values["compact_gz_sha256"]}
    for field in ("profile","source_local_index","cnf_clauses","raw_lrat_bytes","compact_lrat_bytes"):
        try: result[field]=int(result[field])
        except ValueError as error: raise ValueError(f"{tag}: ledger integer malformed") from error
        if result[field]<0: raise ValueError(f"{tag}: ledger integer negative")
    for field in ("cnf_sha256","raw_lrat_sha256","compact_lrat_sha256","gzip_sha256"):
        if SHA.fullmatch(result[field]) is None: raise ValueError(f"{tag}: ledger SHA malformed")
    return result

def selected_ledgers(path,pin,rows,coverage_rows,coverage_path,coverage_pin,inventory_path,inventory_pin,profile_counts):
    receipt=read_canonical(path,pin,"selected ledger receipt")
    fields={"capacity_inventory_path","capacity_inventory_sha256","coverage_receipt_path",
        "coverage_receipt_sha256","inventory_helper_path","inventory_helper_sha256","leaf_count","ledger_roots",
        "producer_path","producer_sha256",
        "profile_counts","schema","selected_ledger_identity_sha256","snapshot_path","snapshot_sha256"}
    if (set(receipt)!=fields or receipt.get("schema")!=LEDGER_RECEIPT_SCHEMA
            or receipt.get("coverage_receipt_sha256")!=coverage_pin
            or receipt.get("coverage_receipt_path")!=str(coverage_path)
            or receipt.get("capacity_inventory_sha256")!=inventory_pin
            or receipt.get("capacity_inventory_path")!=str(inventory_path)
            or receipt.get("leaf_count")!=len(rows) or receipt.get("profile_counts")!=list(profile_counts)
            or receipt.get("snapshot_path")!="selected-ledgers.json"
            or set(receipt.get("ledger_roots",{}))!={"host","v2","v3"}):
        raise ValueError("selected ledger receipt mismatch")
    for value in receipt["ledger_roots"].values():
        if set(value)!={"count","identity_sha256","path"} or type(value["count"]) is not int \
                or value["count"]<0 or SHA.fullmatch(str(value["identity_sha256"])) is None:
            raise ValueError("selected ledger root identity malformed")
    producer=Path(receipt["producer_path"])
    if (producer!=Path(SNAPSHOT.__file__).resolve() or receipt.get("producer_sha256")!=SNAPSHOT_PRODUCER_SHA256
            or sha(producer)!=SNAPSHOT_PRODUCER_SHA256):
        raise ValueError("ledger snapshot producer path/hash mismatch")
    require_file(producer,receipt["producer_sha256"],"ledger snapshot producer")
    inventory_helper=Path(receipt["inventory_helper_path"])
    require_file(inventory_helper,receipt["inventory_helper_sha256"],"ledger inventory helper")
    root=path.parent; snapshot_path=root/receipt["snapshot_path"]
    snapshot=read_canonical(snapshot_path,receipt["snapshot_sha256"],"selected ledger snapshot")
    if (set(snapshot)!={"capacity_inventory_sha256","coverage_receipt_sha256","profile_counts","rows","schema"}
            or snapshot.get("schema")!=LEDGER_SCHEMA or snapshot.get("coverage_receipt_sha256")!=coverage_pin
            or snapshot.get("capacity_inventory_sha256")!=inventory_pin
            or snapshot.get("profile_counts")!=list(profile_counts) or not isinstance(snapshot.get("rows"),list)
            or [row.get("tag") for row in snapshot["rows"]]!=[row["tag"] for row in rows]):
        raise ValueError("selected ledger snapshot mismatch")
    selected=[]; paths=[path,snapshot_path,producer,inventory_helper]; identities=[]
    certificate_fields={"p","i","cnf_sha256","cnf_clauses","raw_lrat_sha256","raw_lrat_bytes",
                        "compact_lrat_sha256","compact_bytes","compact_gz_sha256"}
    for inventory,coverage,row in zip(rows,coverage_rows,snapshot["rows"],strict=True):
        if (set(row)!={"capacity_local_index","certificate_identity","selected","sources","tag"}
                or set(row["certificate_identity"])!=certificate_fields
                or set(row["selected"])!={"namespace","path","sha256"}
                or set(row["sources"])!={"host","v2","v3"}):
            raise ValueError("selected ledger row schema mismatch")
        if row["capacity_local_index"]!=inventory["capacity_local_index"]:
            raise ValueError("selected ledger capacity ordering mismatch")
        for key in ("p","i","cnf_clauses","raw_lrat_bytes","compact_bytes"):
            if type(row["certificate_identity"][key]) is not int or row["certificate_identity"][key]<0:
                raise ValueError("selected ledger certificate integer malformed")
        for key in ("cnf_sha256","raw_lrat_sha256","compact_lrat_sha256","compact_gz_sha256"):
            if SHA.fullmatch(str(row["certificate_identity"][key])) is None:
                raise ValueError("selected ledger certificate SHA malformed")
        present=[]
        for source_namespace,source in row["sources"].items():
            if source is None: continue
            if (set(source)!={"namespace","source_path","sha256"} or source["namespace"]!=source_namespace
                    or not Path(source["source_path"]).is_absolute() or SHA.fullmatch(str(source["sha256"])) is None):
                raise ValueError("selected ledger provenance malformed")
            present.append(source_namespace)
        namespace=row["selected"]["namespace"]
        relative=row["selected"]["path"]
        expected_namespace=next((name for name in ("v3","v2","host") if name in present),None)
        if namespace!=expected_namespace or relative!=f"ledgers/{namespace}/{row['tag']}.line":
            raise ValueError("selected ledger relative path mismatch")
        selected_path=root/relative
        require_file(selected_path,row["selected"]["sha256"],"immutable selected ledger")
        parsed=parse_ledger(selected_path,row["selected"]["sha256"],row["tag"],namespace)
        expected={"profile":row["certificate_identity"]["p"],"source_local_index":row["certificate_identity"]["i"],
            "cnf_sha256":row["certificate_identity"]["cnf_sha256"],
            "cnf_clauses":row["certificate_identity"]["cnf_clauses"],
            "raw_lrat_sha256":row["certificate_identity"]["raw_lrat_sha256"],
            "raw_lrat_bytes":row["certificate_identity"]["raw_lrat_bytes"],
            "compact_lrat_sha256":row["certificate_identity"]["compact_lrat_sha256"],
            "compact_lrat_bytes":row["certificate_identity"]["compact_bytes"],
            "gzip_sha256":row["certificate_identity"]["compact_gz_sha256"]}
        if (parsed!=expected or expected["profile"]!=inventory["profile"]
                or not coverage["local_index"].isdigit()
                or expected["source_local_index"]!=int(coverage["local_index"])):
            raise ValueError("selected ledger certificate/coordinate mismatch")
        selected.append({"ledger_namespace":namespace,"ledger_path":str(selected_path),
                         "ledger_sha256":row["selected"]["sha256"],**parsed})
        paths.append(selected_path); identities.append({"bytes":selected_path.stat().st_size,
            "path":relative,"sha256":row["selected"]["sha256"]})
    if hashlib.sha256(canonical(identities)).hexdigest()!=receipt["selected_ledger_identity_sha256"]:
        raise ValueError("selected ledger identity mismatch")
    return selected,paths

def native_identity(path):
    digest=hashlib.sha256(); size=actions=0
    with path.open(encoding="ascii") as stream:
        for number,line in enumerate(stream,1):
            tokens=line.split()
            if not tokens or tokens[0]=="c": continue
            for chunk in ENCODER.encoded_action(tokens,number): digest.update(chunk); size+=len(chunk)
            actions+=1
    return {"bytes":size,"sha256":digest.hexdigest(),"actions":actions}

def unpack7_identity(path):
    digest=hashlib.sha256(); size=0; acc=bits=0
    with path.open("rb") as stream:
        for chunk in iter(lambda:stream.read(1<<20),b""):
            output=bytearray()
            for byte in chunk:
                if byte>=128: raise ValueError("packed payload is not seven-bit")
                acc|=byte<<bits; bits+=7
                while bits>=8: output.append(acc&255); acc>>=8; bits-=8
            digest.update(output); size+=len(output)
    if acc!=0: raise ValueError("packed payload has nonzero padding")
    return {"bytes":size,"sha256":digest.hexdigest()}

def source_index(rows):
    lines=["\t".join(SOURCE_COLUMNS)]
    for row in rows:
        lines.append("\t".join(str(row[key]) for key in SOURCE_COLUMNS))
    return "\n".join(lines)+"\n"

def expected_templates():
    return {
      "compress":["{python}","{compressor}","{binary}","--frame-output","{frame}",
                  "--packed-output","{packed}","--lz4","{lz4}"],
      "decode":["{lz4}","-q","-d","-c","{frame}"],
      "encode":["{python}","{encoder}","{compact}","--binary-output","{binary}"],
      "fetch":["{aws}","s3","cp","--only-show-errors","{s3_key}","{gzip}"],
      "cnf_emit":["{runtime}","run","--rm","--network=none","-v","{work}:/data:ro",
                  "--entrypoint","/cache/bin/v2cnf","{image}","emit","{profile}","/data/table.json"],
      "cnf_check":["{runtime}","run","--rm","--network=none","-v","{work}:/data:ro",
                   "--entrypoint","/cache/bin/v2cnf","{image}","check","{profile}",
                   "/data/table.json","/data/orbit.cnf"],
      "v2cnf_pin":["{runtime}","run","--rm","--network=none","--entrypoint","/usr/bin/sha256sum",
                    "{image}","/cache/bin/v2cnf"],
      "replay":["{runtime}","run","--rm","--network=none","-v","{work}:/data:ro",
                "--entrypoint","/cache/bin/lratreplay","{image}","/data/orbit.cnf","/data/proof.lrat"],
      "replay_pin":["{runtime}","run","--rm","--network=none","--entrypoint","/usr/bin/sha256sum",
                    "{image}","/cache/bin/lratreplay"],
    }

def expand(template,values):
    try: result=[token.format_map(values) for token in template]
    except (KeyError,ValueError) as error: raise ValueError("command template expansion failed") from error
    if any(not token for token in result): raise ValueError("expanded command has an empty argument")
    return result

def command(runner,kind,argv,cwd,environment,stdout,stderr):
    result=runner(kind,argv,cwd,environment,stdout,stderr)
    fields={"cumulative_children_maxrss_kb","rc","system_ns","user_ns","wall_ns"}
    if (not isinstance(result,dict) or set(result)!=fields or result.get("rc")!=0
            or any(type(result.get(key)) is not int or result[key]<0 for key in fields)
            or result["cumulative_children_maxrss_kb"]<=0 or result["wall_ns"]<=0):
        raise ValueError(f"{kind} command failed or returned malformed metrics")
    if (not stdout.is_absolute() or stdout.is_symlink() or not stdout.is_file()
            or not stderr.is_absolute() or stderr.is_symlink() or not stderr.is_file()):
        raise ValueError(f"{kind} command logs malformed")
    core={"argv":argv,"cwd":str(cwd),"environment":environment,"kind":kind}
    return {**core,**result,"command_identity_sha256":hashlib.sha256(canonical(core)).hexdigest(),
            "stdout_sha256":sha(stdout),"stderr_sha256":sha(stderr),
            "stdout_bytes":stdout.stat().st_size,"stderr_bytes":stderr.stat().st_size}

def command_json(path,fields,label):
    raw=path.read_bytes()
    try: value=json.loads(raw)
    except (UnicodeDecodeError,json.JSONDecodeError) as error: raise ValueError(f"{label} output is not JSON") from error
    expected=(json.dumps(value,sort_keys=True)+"\n").encode("ascii")
    if (not isinstance(value,dict) or set(value)!=set(fields) or raw!=expected):
        raise ValueError(f"{label} output schema/canonicalization mismatch")
    return value

def fsync_directories(root):
    directories=[path for path in root.rglob("*") if path.is_dir()]
    for directory in sorted(directories,key=lambda path:len(path.parts),reverse=True)+[root]:
        descriptor=os.open(directory,os.O_RDONLY)
        try: os.fsync(descriptor)
        finally: os.close(descriptor)

def build(coverage_receipt,coverage_sha256,capacity_inventory,capacity_inventory_sha256,
          ledger_snapshot,ledger_snapshot_sha256,toolchain,toolchain_sha256,output,
          runner,profile_counts=PROFILE_COUNTS):
    producer=Path(__file__).resolve(); producer_pin=sha(producer)
    require_file(capacity_inventory,capacity_inventory_sha256,"capacity inventory")
    rows=inventory_rows(capacity_inventory,profile_counts)
    snapshot_rows=[{"local_index":row["capacity_local_index"],"profile":row["profile"],"tag":row["tag"]}
                   for row in rows]
    coverage,coverage_rows,captured=SNAPSHOT.terminal_coverage(coverage_receipt,coverage_sha256,
        capacity_inventory,capacity_inventory_sha256,snapshot_rows)
    ledgers,ledger_paths=selected_ledgers(ledger_snapshot,ledger_snapshot_sha256,rows,coverage_rows,
        coverage_receipt,coverage_sha256,capacity_inventory,capacity_inventory_sha256,profile_counts)
    tools=read_canonical(toolchain,toolchain_sha256,"toolchain contract")
    tool_fields={"aws_path","aws_sha256","command_identity_derivation","command_templates",
                 "compressor_sha256","container_runtime_path","container_runtime_sha256",
                 "encoder_sha256","environments","image","lratreplay_sha256","lz4_args","lz4_path",
                 "lz4_sha256","lz4_version","python_path","python_sha256",
                 "v2cnf_sha256",
                 "producer_helpers","schema"}
    if (set(tools)!=tool_fields or tools.get("schema")!=TOOLCHAIN_SCHEMA
            or tools.get("image")!=IMAGE or tools.get("lratreplay_sha256")!=LRATREPLAY_SHA256
            or any(SHA.fullmatch(str(tools.get(key))) is None for key in
                   ("aws_sha256","compressor_sha256","container_runtime_sha256","encoder_sha256",
                    "lratreplay_sha256","lz4_sha256","python_sha256","v2cnf_sha256"))
            or tools.get("lz4_args")!=["-q","-f","-12","-T1","-BI","-B7","--content-size","--no-frame-crc"]):
        raise ValueError("toolchain contract mismatch")
    helpers=[{"source":name,"sha256":sha(HERE/name)} for name in
             ("filter_h1_capacity_inventory.py","encode_h1_v2_binary_lrat.py","compress_h1_v2_binary_lrat.py")]
    if (tools["producer_helpers"]!=helpers or tools["encoder_sha256"]!=helpers[1]["sha256"]
            or tools["compressor_sha256"]!=helpers[2]["sha256"]):
        raise ValueError("toolchain helper identity mismatch")
    if (tools["command_templates"]!=expected_templates()
            or tools["command_identity_derivation"]!="sha256(canonical-json({argv,cwd,environment,kind}))"
            or set(tools["environments"])!=set(expected_templates())
            or any(not isinstance(env,dict) or any(not isinstance(key,str) or not isinstance(value,str)
                   for key,value in env.items()) for env in tools["environments"].values())):
        raise ValueError("toolchain command contract mismatch")
    lz4_path=Path(tools["lz4_path"]); require_file(lz4_path,tools["lz4_sha256"],"lz4 tool")
    aws_path=Path(tools["aws_path"]); require_file(aws_path,tools["aws_sha256"],"AWS CLI")
    runtime_path=Path(tools["container_runtime_path"])
    require_file(runtime_path,tools["container_runtime_sha256"],"container runtime")
    python_path=Path(tools["python_path"]); require_file(python_path,tools["python_sha256"],"Python runtime")
    if python_path!=Path(sys.executable).resolve(): raise ValueError("Python runtime path mismatch")
    if (not output.is_absolute() or output!=output.resolve(strict=False) or output.is_symlink() or output.exists()
            or not output.parent.is_dir() or output.parent.is_symlink()):
        raise ValueError("output must be absent under an existing real directory")
    captured=[producer,capacity_inventory,ledger_snapshot,toolchain,lz4_path,aws_path,runtime_path,
              python_path,
              *[HERE/item["source"] for item in helpers],
              *captured,*ledger_paths]
    pins={str(path):sha(path) for path in captured}
    bucket=coverage["aws"]["bucket"]; prefix=coverage["aws"]["s3_prefix"].strip("/")
    fetch_environment=tools["environments"]["fetch"]
    home=Path(fetch_environment["HOME"]) if fetch_environment.get("HOME") else None
    config=Path(fetch_environment["AWS_CONFIG_FILE"]) if fetch_environment.get("AWS_CONFIG_FILE") else None
    credentials=Path(fetch_environment["AWS_SHARED_CREDENTIALS_FILE"]) \
        if fetch_environment.get("AWS_SHARED_CREDENTIALS_FILE") else None
    if (fetch_environment.get("AWS_PROFILE")!=coverage["aws"]["profile"]
            or set(fetch_environment)-{"AWS_PROFILE","AWS_CONFIG_FILE","AWS_SHARED_CREDENTIALS_FILE",
                                        "AWS_EC2_METADATA_DISABLED","HOME"}
            or not (fetch_environment.get("HOME") or
                    (fetch_environment.get("AWS_CONFIG_FILE") and fetch_environment.get("AWS_SHARED_CREDENTIALS_FILE")))
            or (home is not None and (not home.is_absolute() or home!=home.resolve() or home.is_symlink()
                                      or not home.is_dir()))
            or (home is None and any(path is None or not path.is_absolute() or path!=path.resolve()
                                     or path.is_symlink() or not path.is_file()
                                     for path in (config,credentials)))
            or any(tools["environments"][kind]!={} for kind in set(expected_templates())-{"fetch"})):
        raise ValueError("toolchain AWS profile mismatch")
    with tempfile.TemporaryDirectory(prefix=".h1-capacity-bank-stage-",dir=output.parent) as raw:
        stage=Path(raw); payload_rows=[]; audit_rows=[]; staged=[]
        for inventory,coverage_row,ledger in zip(rows,coverage_rows,ledgers,strict=True):
            tag=inventory["tag"]; work=stage/tag; work.mkdir()
            if (coverage_row["profile"]!=str(inventory["profile"])
                    or coverage_row["family"]!=PROFILE_NAMES[inventory["profile"]]
                    or coverage_row["inventory_source"] not in ("all_even_capacity","non_all_even_capacity")
                    or not coverage_row["local_index"].isdigit()
                    or ledger["source_local_index"]!=int(coverage_row["local_index"])):
                raise ValueError(f"{tag}: manifest/coverage/ledger coordinate mismatch")
            gz=work/"proof.lrat.gz"; compact=work/"proof.lrat"; cnf=work/"orbit.cnf"
            key=f"s3://{bucket}/{prefix}/h1/{tag}.compact.lrat.gz"
            profile,*table_values=inventory["inventory_line"].split()
            if profile!=str(inventory["profile"]) or len(table_values)!=len(FILTER.TABLE_PAIRS):
                raise ValueError(f"{tag}: inventory v2cnf arguments mismatch")
            table_object=[[[left,right],int(value)] for (left,right),value in
                          zip(FILTER.TABLE_PAIRS,table_values,strict=True) if value!="0"]
            table_raw=(json.dumps(table_object)+"\n").encode("ascii")
            if hashlib.sha1(table_raw[:-1]).hexdigest()[:16]!=tag:
                raise ValueError(f"{tag}: canonical v2cnf table/tag mismatch")
            table=work/"table.json"; table.write_bytes(table_raw)
            values={"aws":str(aws_path),"binary":str(work/"proof.bin"),"cnf":str(cnf),
                "compact":str(compact),"compressor":str(HERE/"compress_h1_v2_binary_lrat.py"),
                "encoder":str(HERE/"encode_h1_v2_binary_lrat.py"),"frame":str(work/"proof.lz4"),
                "gzip":str(gz),"image":tools["image"],"lz4":str(lz4_path),
                "packed":str(work/"proof.lz4p7"),"profile":profile,"python":str(python_path),
                "runtime":str(runtime_path),"s3_key":key,"tag":tag,"work":str(work)}
            records={}; retained=[]
            def invoke(kind,stdout_override=None,retain_stdout=True):
                stdout=stdout_override or work/f"{kind}.stdout"; stderr=work/f"{kind}.stderr"
                record=command(runner,kind,expand(tools["command_templates"][kind],values),work,
                               tools["environments"][kind],stdout,stderr)
                out_relative=f"logs/{tag}.{kind}.stdout"; err_relative=f"logs/{tag}.{kind}.stderr"
                record={**record,"stdout_path":out_relative if retain_stdout else None,"stderr_path":err_relative}
                records[kind]=record
                if retain_stdout: retained.append((stdout,out_relative))
                retained.append((stderr,err_relative))
                return stdout
            invoke("fetch")
            require_file(gz,ledger["gzip_sha256"],f"{tag} fetched gzip")
            gzip_bytes=gz.stat().st_size
            try:
                with gzip.open(gz,"rb") as source,compact.open("xb") as target: shutil.copyfileobj(source,target)
            except Exception as error: raise ValueError(f"{tag}: gzip decode failed") from error
            require_file(compact,ledger["compact_lrat_sha256"],f"{tag} compact proof")
            if compact.stat().st_size!=ledger["compact_lrat_bytes"]: raise ValueError(f"{tag}: compact byte mismatch")
            native=native_identity(compact); compact_actions=native["actions"]
            v2cnf_pin_stdout=invoke("v2cnf_pin")
            if v2cnf_pin_stdout.read_text().split()!=[tools["v2cnf_sha256"],"/cache/bin/v2cnf"]:
                raise ValueError(f"{tag}: v2cnf container pin mismatch")
            invoke("cnf_emit",cnf,False)
            require_file(cnf,ledger["cnf_sha256"],f"{tag} rematerialized CNF")
            with cnf.open() as cnf_stream:
                header=next((line.split() for line in cnf_stream if line.startswith("p cnf ")),None)
            if header is None or int(header[3])!=ledger["cnf_clauses"]: raise ValueError(f"{tag}: CNF clause mismatch")
            check_stdout=invoke("cnf_check")
            check_match=re.fullmatch(r"MATCH \(([0-9]+) clauses, top ([0-9]+)\)\n",
                                     check_stdout.read_text(encoding="utf-8"))
            if check_match is None or int(check_match.group(1))!=ledger["cnf_clauses"]:
                raise ValueError(f"{tag}: independent v2cnf check mismatch")
            if table.read_bytes()!=table_raw:
                raise ValueError(f"{tag}: canonical v2cnf table drift")
            pin_stdout=invoke("replay_pin"); replay_stdout=invoke("replay")
            if (pin_stdout.read_text().split()!=[tools["lratreplay_sha256"],"/cache/bin/lratreplay"]
                    or replay_stdout.read_text().splitlines()[-1:]!=["LRAT accepted: true"]):
                raise ValueError(f"{tag}: independent replay logs mismatch")
            binary,frame,packed=work/"proof.bin",work/"proof.lz4",work/"proof.lz4p7"
            encode_stdout=invoke("encode"); compress_stdout=invoke("compress")
            decoded=work/"decoded.bin"; invoke("decode",decoded,False)
            for artifact,label in ((binary,"binary"),(frame,"frame"),(packed,"packed"),(decoded,"decoded")):
                if not artifact.is_file() or artifact.is_symlink(): raise ValueError(f"{tag}: {label} output malformed")
            encoding={"binary_bytes":binary.stat().st_size,"binary_sha256":sha(binary),
                "frame_bytes":frame.stat().st_size,"frame_sha256":sha(frame),
                "packed_bytes":packed.stat().st_size,"packed_sha256":sha(packed)}
            encoder_report=command_json(encode_stdout,
                {"actions","binary_bytes","binary_sha256","packed_bytes","packed_sha256"},f"{tag}: encoder")
            compressor_report=command_json(compress_stdout,
                {"binary_bytes","binary_sha256","frame_bytes","frame_sha256","lz4_args","lz4_bytes",
                 "lz4_sha256","lz4_version","packed_bytes","packed_sha256"},f"{tag}: compressor")
            if (encoder_report!={"actions":compact_actions,"binary_bytes":encoding["binary_bytes"],
                    "binary_sha256":encoding["binary_sha256"],"packed_bytes":0,
                    "packed_sha256":hashlib.sha256(b"").hexdigest()}
                    or compressor_report!={"binary_bytes":encoding["binary_bytes"],
                    "binary_sha256":encoding["binary_sha256"],"frame_bytes":encoding["frame_bytes"],
                    "frame_sha256":encoding["frame_sha256"],"lz4_args":tools["lz4_args"],
                    "lz4_bytes":lz4_path.stat().st_size,"lz4_sha256":tools["lz4_sha256"],
                    "lz4_version":tools["lz4_version"],"packed_bytes":encoding["packed_bytes"],
                    "packed_sha256":encoding["packed_sha256"]}):
                raise ValueError(f"{tag}: helper JSON evidence mismatch")
            if (encoding["binary_sha256"]!=native["sha256"] or encoding["binary_bytes"]!=native["bytes"]
                    or unpack7_identity(packed)!={"bytes":encoding["frame_bytes"],"sha256":encoding["frame_sha256"]}
                    or identity(decoded)!={"bytes":native["bytes"],"path":str(decoded),"sha256":native["sha256"]}):
                raise ValueError(f"{tag}: payload roundtrip mismatch")
            relative=f"packed/{encoding['packed_sha256'][:2]}/{encoding['packed_sha256']}.lrat.lz4p7"
            replay_relative=f"replay/{tag}.json"; out_relative=f"logs/{tag}.stdout"; err_relative=f"logs/{tag}.stderr"
            evidence={"accepted_marker":"LRAT accepted: true","commands":records,
                "cnf_sha256":ledger["cnf_sha256"],"compact_bytes":ledger["compact_lrat_bytes"],
                "compact_lrat_sha256":ledger["compact_lrat_sha256"],
                "image":tools["image"],"lratreplay_sha256":tools["lratreplay_sha256"],
                "schema":REPLAY_SCHEMA,"table_path":f"tables/{tag}.json",
                "table_sha256":hashlib.sha256(table_raw).hexdigest(),"tag":tag}
            evidence_path=work/"replay.json"; evidence_path.write_bytes(canonical(evidence))
            selected_source=Path(ledger["ledger_path"]); ledger_relative=f"ledgers/{ledger['ledger_namespace']}/{tag}.line"
            payload={"binary_bytes":encoding["binary_bytes"],"binary_lrat_sha256":encoding["binary_sha256"],
                "capacity_local_index":inventory["capacity_local_index"],"cnf_sha256":ledger["cnf_sha256"],
                "compact_bytes":ledger["compact_lrat_bytes"],"compact_lrat_sha256":ledger["compact_lrat_sha256"],
                "gzip_bytes":gzip_bytes,"gzip_sha256":ledger["gzip_sha256"],
                "ledger_namespace":ledger["ledger_namespace"],"ledger_path":ledger_relative,
                "ledger_sha256":ledger["ledger_sha256"],"lrat_actions":compact_actions,
                "lz4_frame_bytes":encoding["frame_bytes"],"lz4_frame_sha256":encoding["frame_sha256"],
                "packed_lz4_bytes":encoding["packed_bytes"],"packed_lz4_path":relative,
                "packed_lz4_sha256":encoding["packed_sha256"],"profile":inventory["profile"],
                "raw_lrat_bytes":ledger["raw_lrat_bytes"],"raw_lrat_sha256":ledger["raw_lrat_sha256"],
                "s3_key":key,"source_cnf_clauses":ledger["cnf_clauses"],"tag":tag}
            payload_rows.append(payload)
            audit_rows.append({"ledger_namespace":ledger["ledger_namespace"],"ledger_sha256":ledger["ledger_sha256"],
                "packed_lz4_sha256":encoding["packed_sha256"],"replay_evidence_path":replay_relative,
                "replay_evidence_sha256":sha(evidence_path),
                "replay_command_identity_sha256":records["replay"]["command_identity_sha256"],
                "s3_key":key,"tag":tag})
            staged.append({"files":[(packed,relative),(evidence_path,replay_relative),
                           (table,f"tables/{tag}.json"),
                           (selected_source,ledger_relative),*retained],"evidence":(evidence_path,replay_relative),
                           "table":(table,f"tables/{tag}.json",table_raw)})
        payload_index={"capacity_inventory_sha256":capacity_inventory_sha256,"profile_counts":list(profile_counts),
                       "rows":payload_rows,"schema":PAYLOAD_SCHEMA}
        replay_identity=hashlib.sha256(canonical(audit_rows)).hexdigest()
        replay_audit={"capacity_inventory_sha256":capacity_inventory_sha256,
            "coverage_receipt_sha256":coverage_sha256,"profile_counts":list(profile_counts),"rows":audit_rows,
            "replay_evidence_identity_sha256":replay_identity,"schema":AUDIT_SCHEMA}
        index_rows=[{"orbit":row["tag"],"profile":PROFILE_NAMES[row["profile"]],
            "localIndex":row["capacity_local_index"],"compact_lrat_sha256":row["compact_lrat_sha256"],
            "raw_lrat_sha256":row["raw_lrat_sha256"],"cnf_sha256":row["cnf_sha256"],
            "lrat_actions":row["lrat_actions"],"source_cnf_clauses":row["source_cnf_clauses"],
            "compact_bytes":row["compact_bytes"],"stub_ready":1,"binary_lrat_sha256":row["binary_lrat_sha256"],
            "binary_bytes":row["binary_bytes"],"lz4_frame_sha256":row["lz4_frame_sha256"],
            "lz4_frame_bytes":row["lz4_frame_bytes"],"packed_lz4_sha256":row["packed_lz4_sha256"],
            "packed_lz4_bytes":row["packed_lz4_bytes"]} for row in payload_rows]
        index_raw=source_index(index_rows).encode("ascii")
        payload_identity=hashlib.sha256(canonical([{"path":row["packed_lz4_path"],
            "sha256":row["packed_lz4_sha256"],"bytes":row["packed_lz4_bytes"]} for row in payload_rows])).hexdigest()
        recheck(pins,"input drift before publication")
        publication=stage/"publication"; publication.mkdir()
        for item in staged:
            for source,relative_path in item["files"]:
                destination=publication/relative_path; destination.parent.mkdir(parents=True,exist_ok=True)
                if destination.exists():
                    if destination.read_bytes()!=source.read_bytes(): raise ValueError("content-address collision")
                    continue
                with source.open("rb") as incoming,destination.open("xb") as outgoing:
                    shutil.copyfileobj(incoming,outgoing); outgoing.flush(); os.fsync(outgoing.fileno())
        named=(("source-index.tsv",index_raw),("payload-index.json",canonical(payload_index)),
               ("replay-audit.json",canonical(replay_audit)),("toolchain.json",canonical(tools)))
        for name,data in named:
            with (publication/name).open("xb") as stream: stream.write(data); stream.flush(); os.fsync(stream.fileno())
        receipt={"all_even_manifest_path":coverage["inputs"]["all_even_manifest"],
            "all_even_manifest_sha256":coverage["inputs"]["all_even_manifest_sha256"],
            "capacity_inventory_path":str(capacity_inventory),"capacity_inventory_sha256":capacity_inventory_sha256,
            "compact_universe_path":coverage["inputs"]["compact_inventory"],
            "compact_universe_sha256":coverage["inputs"]["compact_inventory_sha256"],
            "complement_manifest_path":coverage["inputs"]["complement_manifest"],
            "complement_manifest_sha256":coverage["inputs"]["complement_manifest_sha256"],
            "coverage_receipt_path":str(coverage_receipt),"coverage_receipt_sha256":coverage_sha256,
            "coverage_terminal_counts":{"certified":coverage["summary"]["certified"],
                "fleet_in_flight":coverage["summary"]["fleet_in_flight"],
                "pending":coverage["summary"]["pending"],"status_total":coverage["summary"]["status_total"]},
            "leaf_count":sum(profile_counts),"ledger_snapshot_path":str(ledger_snapshot),
            "ledger_snapshot_sha256":ledger_snapshot_sha256,"materializer_sha256":producer_pin,
            "materializer_source":"research/problems/erdos-85-wip-01/sat49/materialize_h1_capacity_payload_bank.py",
            "payload_identity_sha256":payload_identity,"payload_index_path":str(output/"payload-index.json"),
            "payload_index_sha256":sha(publication/"payload-index.json"),"profile_counts":list(profile_counts),
            "replay_audit_path":str(output/"replay-audit.json"),"replay_audit_sha256":sha(publication/"replay-audit.json"),
            "s3_bucket":bucket,"s3_prefix":prefix,
            "selected_ledger_identity_sha256":read_canonical(ledger_snapshot,ledger_snapshot_sha256,
                "selected ledger receipt")["selected_ledger_identity_sha256"],
            "schema":BANK_SCHEMA,"source_index_path":str(output/"source-index.tsv"),
            "source_index_sha256":sha(publication/"source-index.tsv"),"toolchain_path":str(output/"toolchain.json"),
            "toolchain_sha256":sha(publication/"toolchain.json")}
        recheck(pins,"input drift before receipt")
        if output.parent.is_symlink() or output.parent!=output.parent.resolve() or not output.parent.is_dir():
            raise ValueError("output parent drift before receipt")
        for name,data in named:
            if (publication/name).read_bytes()!=data: raise ValueError("nested schema/output drift before receipt")
        for item in staged:
            if any((publication/relative).read_bytes()!=source.read_bytes() for source,relative in item["files"]):
                raise ValueError("retained evidence/log/ledger drift before receipt")
            table_path,table_relative,table_expected=item["table"]
            if table_path.read_bytes()!=table_expected or (publication/table_relative).read_bytes()!=table_expected:
                raise ValueError("canonical v2cnf table drift before receipt")
        for row in payload_rows:
            path=publication/row["packed_lz4_path"]
            if sha(path)!=row["packed_lz4_sha256"] or path.stat().st_size!=row["packed_lz4_bytes"]:
                raise ValueError("published payload drift")
        receipt_raw=canonical(receipt)
        with (publication/"receipt.json").open("xb") as stream:
            stream.write(receipt_raw); stream.flush(); os.fsync(stream.fileno())
        if (publication/"receipt.json").read_bytes()!=receipt_raw:
            raise ValueError("receipt drift before atomic publication")
        fsync_directories(publication)
        if output.exists() or output.is_symlink(): raise ValueError("output appeared before atomic publication")
        publication.rename(output)
        descriptor=os.open(output.parent,os.O_RDONLY)
        try: os.fsync(descriptor)
        finally: os.close(descriptor)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ("coverage-receipt","capacity-inventory","ledger-snapshot","toolchain"):
        parser.add_argument(f"--{name}",type=Path,required=True); parser.add_argument(f"--{name}-sha256",required=True)
    parser.add_argument("--output",type=Path,required=True)
    args=parser.parse_args()
    def runner(kind,argv,cwd,environment,stdout,stderr):
        before=resource.getrusage(resource.RUSAGE_CHILDREN); started=time.monotonic_ns()
        with stdout.open("xb") as out,stderr.open("xb") as err:
            result=subprocess.run(argv,cwd=cwd,env=environment,stdout=out,stderr=err)
            out.flush(); err.flush(); os.fsync(out.fileno()); os.fsync(err.fileno())
        after=resource.getrusage(resource.RUSAGE_CHILDREN)
        return {"cumulative_children_maxrss_kb":max(1,int(after.ru_maxrss)),"rc":result.returncode,
            "system_ns":max(0,int((after.ru_stime-before.ru_stime)*1_000_000_000)),
            "user_ns":max(0,int((after.ru_utime-before.ru_utime)*1_000_000_000)),
            "wall_ns":max(1,time.monotonic_ns()-started)}
    build(args.coverage_receipt,args.coverage_receipt_sha256,args.capacity_inventory,
        args.capacity_inventory_sha256,args.ledger_snapshot,args.ledger_snapshot_sha256,
        args.toolchain,args.toolchain_sha256,args.output,runner)
    print(f"WROTE {args.output} capacity={sum(PROFILE_COUNTS)}")

if __name__=="__main__": main()
