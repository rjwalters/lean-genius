#!/usr/bin/env python3
import importlib.util,json,os,sys,tempfile,unittest
from pathlib import Path
from unittest import mock

HERE=Path(__file__).resolve().parent
def load(name,path):
 spec=importlib.util.spec_from_file_location(name,path); module=importlib.util.module_from_spec(spec)
 assert spec.loader is not None; sys.modules[name]=module; spec.loader.exec_module(module); return module
MOD=load("h1_wrapper_final",HERE/"finalize_h1_wrapper_endpoint_receipt.py")
AX=load("h1_axiom",HERE/"audit_h1_endpoint_axioms.py")
AX_TEST=load("h1_axiom_test",HERE/"test_audit_h1_endpoint_axioms.py")
AGG=load("h1_aggregate",HERE/"generate_h1_v2_lean_aggregate.py")
MAT=load("h1_materializer",HERE/"materialize_h1_capacity_payload_bank.py")

def fixture(root):
 root=root.resolve(); audit_args,_,_=AX_TEST.fixture(root); audit_args["output"]=root/"axiom"
 AX.build(**audit_args); axiom_path=audit_args["output"]/"receipt.json"; axiom=json.loads(axiom_path.read_text())
 repo=audit_args["repo"]
 producer_sources={MOD.AXIOM_PRODUCER:HERE/"audit_h1_endpoint_axioms.py",
  MOD.COLD_PRODUCER:HERE/"run_h1_endpoint_cold_build.py",
  MOD.CACHE_PRODUCER:HERE/"snapshot_h1_offline_dependency_cache.py",
  MOD.POST_PRODUCER:HERE/"finalize_h1_leaf_module_evidence.py",
  MOD.FINAL_PRODUCER:HERE/"finalize_h1_wrapper_endpoint_receipt.py",
  MOD.BANK_PRODUCER:HERE/"materialize_h1_capacity_payload_bank.py",
  MOD.REINDEX_PRODUCER:HERE/"reindex_h1_v2_capacity_certificates.py",
  MOD.LAYOUT_PRODUCER:HERE/"generate_h1_v2_lean_aggregate.py",
  MOD.ADAPTER_PRODUCER:HERE/"generate_h1_post_aggregate_adapter.py",
  MOD.LEDGER_PRODUCER:HERE/"snapshot_h1_capacity_selected_ledgers.py",
  "research/problems/erdos-85-wip-01/sat49/filter_h1_capacity_inventory.py":HERE/"filter_h1_capacity_inventory.py",
  "research/problems/erdos-85-wip-01/sat49/encode_h1_v2_binary_lrat.py":HERE/"encode_h1_v2_binary_lrat.py",
  "research/problems/erdos-85-wip-01/sat49/compress_h1_v2_binary_lrat.py":HERE/"compress_h1_v2_binary_lrat.py",
  AX.AUDITOR:HERE.parents[3]/AX.AUDITOR,AX.HELPER:HERE.parents[3]/AX.HELPER}
 for text,source in producer_sources.items():
  destination=repo/text; destination.parent.mkdir(parents=True,exist_ok=True); destination.write_bytes(source.read_bytes())
 sources={MOD.SOURCE:b"import Proofs.Generated.H1\n\ntheorem endpoint : True := by trivial\n",
  "proofs/Proofs/Generated/Leaf.lean":b"import Proofs.Support\ntheorem Erdos85.endpointRoot : True := by trivial\n",
  "proofs/Proofs/Generated/Aggregate.lean":b"import Proofs.Generated.Leaf\ntheorem Erdos85.aggregate : True := by trivial\n",
  "proofs/Proofs/Generated/H1.lean":b"import Proofs.Generated.Aggregate\ntheorem Erdos85.h1 : True := by trivial\n",
  "proofs/Proofs/Support.lean":b"theorem Erdos85.support : True := by trivial\n"}
 for text,raw in sources.items(): path=repo/text; path.parent.mkdir(parents=True,exist_ok=True); path.write_bytes(raw)
 snapshot_path=Path(axiom["cache_snapshot_receipt_path"]); snapshot=json.loads(snapshot_path.read_text())
 manifest={"packages":[{"name":row["name"],"rev":row["rev"],"url":row["manifest_url"]} for row in snapshot["packages"]]}
 control_raw={"proofs/lean-toolchain":b"leanprover/lean4:test\n","proofs/lakefile.toml":b"name = \"test\"\n",
              "proofs/lake-manifest.json":json.dumps(manifest,separators=(",",":"),sort_keys=True).encode()+b"\n"}
 for row in snapshot["control_files"]:
  path=repo/row["path"]; path.parent.mkdir(parents=True,exist_ok=True); path.write_bytes(control_raw[row["path"]])
  row.update({"blob_oid":"a"*40,"bytes":path.stat().st_size,"sha256":MOD.sha(path)})
 snapshot_path.write_bytes(MOD.canonical(snapshot)); axiom["cache_snapshot_receipt_sha256"]=MOD.sha(snapshot_path)
 cold_path=Path(axiom["cold_receipt_path"]); cold=json.loads(cold_path.read_text())
 cold["cache_snapshot_receipt_sha256"]=MOD.sha(snapshot_path); cold["reviewed_control_files"]=snapshot["control_files"]
 post_path=Path(cold["post_module_receipt_path"]); post=json.loads(post_path.read_text())
 evidence_path=post_path.parent/post["evidence_path"]; evidence=json.loads(evidence_path.read_text())
 bank_root=Path(post["bank_receipt_path"]).parent
 zero="0"*64
 def synthetic(label,tag): return __import__("hashlib").sha256(f"{label}:{tag}".encode()).hexdigest()
 for row in evidence["rows"]:
  for label,path_key,hash_key in (("ledger","ledger_path","ledger_sha256"),("packed","packed_path","packed_sha256")):
   row[path_key]=f"{label}/{row['tag']}.bin"; target=bank_root/row[path_key]; target.parent.mkdir(parents=True,exist_ok=True)
   target.write_bytes(f"{label}:{row['tag']}\n".encode()); row[hash_key]=MOD.sha(target)
 table=bank_root/"tables/v2cnf.tsv"; table.parent.mkdir(parents=True,exist_ok=True); table.write_bytes(b"table\n")
 command_log=bank_root/"logs/shared.log"; command_log.parent.mkdir(parents=True,exist_ok=True); command_log.write_bytes(b"log\n")
 command_kinds={"cnf_check","cnf_emit","compress","decode","encode","fetch","replay","replay_pin","v2cnf_pin"}
 replay_command_ids={}
 for row in evidence["rows"]:
  commands={}
  for kind in command_kinds:
   core={"argv":[kind],"cwd":str(bank_root),"environment":{},"kind":kind}
   commands[kind]={**core,"command_identity_sha256":__import__("hashlib").sha256(MOD.canonical(core)).hexdigest(),
    "cumulative_children_maxrss_kb":1,"rc":0,"stderr_bytes":command_log.stat().st_size,
    "stderr_path":"logs/shared.log","stderr_sha256":MOD.sha(command_log),"stdout_bytes":command_log.stat().st_size,
    "stdout_path":"logs/shared.log","stdout_sha256":MOD.sha(command_log),"system_ns":0,"user_ns":0,"wall_ns":1}
  replay_command_ids[row["tag"]]=commands["replay"]["command_identity_sha256"]
  row["replay_evidence_path"]=f"replay/{row['tag']}.json"
  replay_value={"accepted_marker":"LRAT accepted: true","cnf_sha256":synthetic("cnf",row["tag"]),"compact_bytes":1,
   "compact_lrat_sha256":synthetic("compact",row["tag"]),"image":MOD.IMAGE,"lratreplay_sha256":zero,"schema":"erdos85-h1-capacity-replay-evidence-v1",
   "table_path":"tables/v2cnf.tsv","table_sha256":MOD.sha(table),"tag":row["tag"],
   "commands":commands}
  target=bank_root/row["replay_evidence_path"]; target.parent.mkdir(parents=True,exist_ok=True)
  target.write_bytes(MOD.canonical(replay_value)); row["replay_evidence_sha256"]=MOD.sha(target)
 payload_rows=[]; replay_rows=[]
 for row in evidence["rows"]:
  payload_rows.append({"binary_bytes":1,"binary_lrat_sha256":synthetic("binary",row["tag"]),"capacity_local_index":row["capacity_local_index"],
   "cnf_sha256":synthetic("cnf",row["tag"]),"compact_bytes":1,"compact_lrat_sha256":synthetic("compact",row["tag"]),
   "gzip_bytes":1,"gzip_sha256":synthetic("gzip",row["tag"]),
   "ledger_namespace":"host","ledger_path":row["ledger_path"],"ledger_sha256":row["ledger_sha256"],
   "lrat_actions":1,"lz4_frame_bytes":1,"lz4_frame_sha256":synthetic("frame",row["tag"]),
   "packed_lz4_bytes":(bank_root/row["packed_path"]).stat().st_size,
   "packed_lz4_path":row["packed_path"],"packed_lz4_sha256":row["packed_sha256"],"profile":row["profile"],
   "raw_lrat_bytes":1,"raw_lrat_sha256":synthetic("raw",row["tag"]),"s3_key":"test","source_cnf_clauses":1,"tag":row["tag"]})
  replay_rows.append({"ledger_namespace":"host","ledger_sha256":row["ledger_sha256"],
   "packed_lz4_sha256":row["packed_sha256"],"replay_evidence_path":row["replay_evidence_path"],
   "replay_evidence_sha256":row["replay_evidence_sha256"],"replay_command_identity_sha256":replay_command_ids[row["tag"]],
   "s3_key":"test","tag":row["tag"]})
 payload={"capacity_inventory_sha256":zero,"profile_counts":MOD.PROFILE_COUNTS,"rows":payload_rows,"schema":MOD.PAYLOAD_SCHEMA}
 replay_audit={"capacity_inventory_sha256":zero,"coverage_receipt_sha256":zero,"profile_counts":MOD.PROFILE_COUNTS,
  "replay_evidence_identity_sha256":__import__("hashlib").sha256(MOD.canonical(replay_rows)).hexdigest(),
  "rows":replay_rows,"schema":MOD.REPLAY_AUDIT_SCHEMA}
 payload_path=bank_root/"payload-index.json"; replay_audit_path=bank_root/"replay-audit.json"
 payload_path.write_bytes(MOD.canonical(payload)); replay_audit_path.write_bytes(MOD.canonical(replay_audit))
 payload_identity=__import__("hashlib").sha256(MOD.canonical([{"bytes":r["packed_lz4_bytes"],
  "path":r["packed_lz4_path"],"sha256":r["packed_lz4_sha256"]} for r in payload_rows])).hexdigest()
 coverage_root=bank_root/"coverage"; coverage_root.mkdir()
 coverage_inputs={}
 for name in ("all_even_manifest","compact_inventory","complement_manifest","publisher","reconciler"):
  path=coverage_root/f"{name}.txt"; path.write_text(name+"\n"); coverage_inputs[name]=str(path); coverage_inputs[name+"_sha256"]=MOD.sha(path)
 unknown_keys=("certified_s3","fleet_v2_claim","fleet_v2_ledger","fleet_v3_claim","fleet_v3_ledger","host_ledger")
 counts={key:0 for key in {"all_even_capacity","capacity_only_error","cnf_sha_comparable_count","compact_inventory_total",
  "compact_only_pre_capacity","fleet_claim_tags","fleet_ledger_rows","fleet_v2_claim_tags","fleet_v2_ledger_rows",
  "fleet_v3_claim_tags","fleet_v3_ledger_rows","host_ledger_rows","non_all_even_capacity"}}
 counts.update({"anomalies":{},"capacity_inventory_total":13351,"certified_s3_tags":13351,
  "compact_inventory_total":13541,"compact_only_pre_capacity":190,
  "cnf_sha_divergent_count":0,"cnf_sha_divergent_tags":[],"fleet_unknown_without_cert":0,
  "status_counts":{"certified-in-S3":13351,"fleet-in-flight":0,"pending":0},"status_total":13351,
  "unknown_tags":{key:[] for key in unknown_keys}})
 (coverage_root/"counts.json").write_bytes(MOD.canonical(counts))
 (coverage_root/"inventory_universe_diff.tsv").write_bytes(b"tag\trelation\tcompact_profile\tcapacity_source\n")
 coverage_header=("tag","profile","family","local_index","inventory_source","status","certified_s3","host_unsat",
  "host_cnf_sha256","host_verdict","fleet_claim","fleet_cnf_sha256","fleet_verdict","cnf_sha_divergent",
  "fleet_v2_claim","fleet_v2_cnf_sha256","fleet_v2_verdict","fleet_v3_claim","fleet_v3_cnf_sha256","fleet_v3_verdict")
 lines=["\t".join(coverage_header)]
 for row in evidence["rows"]:
  values={key:"" for key in coverage_header}; values.update({"tag":row["tag"],"profile":str(row["profile"]),
   "family":"test","local_index":str(row["capacity_local_index"]),"inventory_source":"test",
   "status":"certified-in-S3","certified_s3":"1","cnf_sha_divergent":"0"})
  lines.append("\t".join(values[key] for key in coverage_header))
 (coverage_root/"coverage.tsv").write_text("\n".join(lines)+"\n")
 coverage_outputs={name:{"bytes":(coverage_root/name).stat().st_size,"sha256":MOD.sha(coverage_root/name)}
  for name in ("counts.json","coverage.tsv","inventory_universe_diff.tsv")}
 coverage_summary={"anomalies":{},"certified":13351,"cnf_sha_comparable_count":0,"cnf_sha_divergent_count":0,
  "fleet_claim_tags":0,"fleet_in_flight":0,"fleet_ledger_rows":0,"fleet_unknown_without_cert":0,
  "host_ledger_rows":0,"pending":0,"status_total":13351,"unknown_tags":{key:[] for key in unknown_keys}}
 live_paths={name:str(coverage_root/name) for name in coverage_outputs}
 coverage={"aws":{"bucket":"test","profile":"test","s3_prefix":"test"},
  "host_ledger_snapshot":{"count":0,"identity_sha256":zero},"inputs":coverage_inputs,
  "live_campaign":str(coverage_root),"live_named_output_paths":live_paths,"live_named_outputs_mutated":False,
  "live_outputs_after":coverage_outputs,"live_outputs_before":coverage_outputs,"outputs":coverage_outputs,
  "schema":MOD.COVERAGE_SCHEMA,"summary":coverage_summary,"timestamp_utc":"2026-01-01T00:00:00Z"}
 coverage_path=coverage_root/"receipt.json"; coverage_path.write_bytes(MOD.canonical(coverage))
 replay_audit["coverage_receipt_sha256"]=MOD.sha(coverage_path); replay_audit_path.write_bytes(MOD.canonical(replay_audit))
 capacity_inventory=bank_root/"capacity-inventory.tsv"; capacity_inventory.write_text("tag\tprofile\tlocal_index\n"+"\n".join(
  f"{row['tag']}\t{row['profile']}\t{row['capacity_local_index']}" for row in evidence["rows"])+"\n")
 payload["capacity_inventory_sha256"]=MOD.sha(capacity_inventory); payload_path.write_bytes(MOD.canonical(payload))
 replay_audit["capacity_inventory_sha256"]=MOD.sha(capacity_inventory); replay_audit_path.write_bytes(MOD.canonical(replay_audit))
 selected_identity=__import__("hashlib").sha256(MOD.canonical([{"bytes":(bank_root/row["ledger_path"]).stat().st_size,
  "path":row["ledger_path"],"sha256":row["ledger_sha256"]} for row in payload_rows])).hexdigest()
 ledger_helper=bank_root/"inventory-helper.py"; ledger_helper.write_text("# helper\n")
 ledger_rows=[]
 for row in payload_rows:
  ledger_rows.append({"capacity_local_index":row["capacity_local_index"],"certificate_identity":{
   "p":row["profile"],"i":row["capacity_local_index"],"cnf_sha256":row["cnf_sha256"],"cnf_clauses":1,
   "raw_lrat_sha256":row["raw_lrat_sha256"],"raw_lrat_bytes":1,"compact_lrat_sha256":row["compact_lrat_sha256"],
   "compact_bytes":1,"compact_gz_sha256":row["gzip_sha256"]},"selected":{"namespace":"host",
   "path":row["ledger_path"],"sha256":row["ledger_sha256"]},"sources":{"host":{"namespace":"host",
   "source_path":str(bank_root/row["ledger_path"]),"sha256":row["ledger_sha256"]},"v2":None,"v3":None},
   "tag":row["tag"]})
 ledger_snapshot={"capacity_inventory_sha256":MOD.sha(capacity_inventory),"coverage_receipt_sha256":MOD.sha(coverage_path),
  "profile_counts":MOD.PROFILE_COUNTS,"rows":ledger_rows,"schema":MOD.LEDGER_SCHEMA}
 ledger_snapshot_path=bank_root/"selected-ledgers.json"; ledger_snapshot_path.write_bytes(MOD.canonical(ledger_snapshot))
 ledger_receipt={"capacity_inventory_path":str(capacity_inventory),"capacity_inventory_sha256":MOD.sha(capacity_inventory),
  "coverage_receipt_path":str(coverage_path),"coverage_receipt_sha256":MOD.sha(coverage_path),
  "inventory_helper_path":str(ledger_helper),"inventory_helper_sha256":MOD.sha(ledger_helper),"leaf_count":13351,
  "ledger_roots":{key:{"count":13351 if key=="host" else 0,"identity_sha256":zero,"path":"unused"} for key in ("host","v2","v3")},
  "producer_path":str(repo/MOD.LEDGER_PRODUCER),"producer_sha256":MOD.LEDGER_PRODUCER_SHA256,
  "profile_counts":MOD.PROFILE_COUNTS,"schema":MOD.LEDGER_RECEIPT_SCHEMA,
  "selected_ledger_identity_sha256":selected_identity,"snapshot_path":"selected-ledgers.json",
  "snapshot_sha256":MOD.sha(ledger_snapshot_path)}
 ledger_receipt_path=bank_root/"selected-ledger-receipt.json"; ledger_receipt_path.write_bytes(MOD.canonical(ledger_receipt))
 source_columns=("orbit","profile","localIndex","compact_lrat_sha256","raw_lrat_sha256","cnf_sha256","lrat_actions",
  "source_cnf_clauses","compact_bytes","stub_ready","binary_lrat_sha256","binary_bytes","lz4_frame_sha256",
  "lz4_frame_bytes","packed_lz4_sha256","packed_lz4_bytes")
 source_lines=["\t".join(source_columns)]
 for row in payload_rows:
  values={"orbit":row["tag"],"profile":MOD.PROFILE_NAMES[row["profile"]],
   "localIndex":str(row["capacity_local_index"]),"compact_lrat_sha256":row["compact_lrat_sha256"],
   "raw_lrat_sha256":row["raw_lrat_sha256"],"cnf_sha256":row["cnf_sha256"],
   "lrat_actions":str(row["lrat_actions"]),"source_cnf_clauses":str(row["source_cnf_clauses"]),
   "compact_bytes":str(row["compact_bytes"]),"stub_ready":"1",
   "binary_lrat_sha256":row["binary_lrat_sha256"],"lz4_frame_sha256":row["lz4_frame_sha256"],
   "binary_bytes":str(row["binary_bytes"]),"lz4_frame_bytes":str(row["lz4_frame_bytes"]),
   "packed_lz4_sha256":row["packed_lz4_sha256"],"packed_lz4_bytes":str(row["packed_lz4_bytes"])}
  source_lines.append("\t".join(values[key] for key in source_columns))
 source_index=bank_root/"source-index.tsv"; source_index.write_text("\n".join(source_lines)+"\n")
 bank_tools_dir=bank_root/"tools"; bank_tools_dir.mkdir()
 tool_paths={}
 for key in ("aws","runtime","lz4","python"):
  path=bank_tools_dir/key; path.write_text(key+"\n"); tool_paths[key]=path
 bank_home=bank_tools_dir/"home"; bank_home.mkdir()
 helpers=[{"source":name,"sha256":MOD.sha(repo/"research/problems/erdos-85-wip-01/sat49"/name)} for name in
  ("filter_h1_capacity_inventory.py","encode_h1_v2_binary_lrat.py","compress_h1_v2_binary_lrat.py")]
 bank_tool={"aws_path":str(tool_paths["aws"]),"aws_sha256":MOD.sha(tool_paths["aws"]),
  "command_identity_derivation":"sha256(canonical-json({argv,cwd,environment,kind}))",
  "command_templates":MAT.expected_templates(),"compressor_sha256":helpers[2]["sha256"],
  "container_runtime_path":str(tool_paths["runtime"]),"container_runtime_sha256":MOD.sha(tool_paths["runtime"]),
  "encoder_sha256":helpers[1]["sha256"],"environments":{key:({"AWS_PROFILE":"test","HOME":str(bank_home)}
   if key=="fetch" else {}) for key in MAT.expected_templates()},
  "image":MOD.IMAGE,"lratreplay_sha256":MAT.LRATREPLAY_SHA256,
  "lz4_args":["-q","-f","-12","-T1","-BI","-B7","--content-size","--no-frame-crc"],
  "lz4_path":str(tool_paths["lz4"]),"lz4_sha256":MOD.sha(tool_paths["lz4"]),"lz4_version":"test",
  "python_path":str(tool_paths["python"]),"python_sha256":MOD.sha(tool_paths["python"]),"v2cnf_sha256":zero,
  "producer_helpers":helpers,"schema":MOD.BANK_TOOL_SCHEMA}
 bank_tool_path=bank_root/"toolchain.json"; bank_tool_path.write_bytes(MOD.canonical(bank_tool))
 bank={key:"unused" for key in {"all_even_manifest_path","capacity_inventory_path","compact_universe_path",
  "complement_manifest_path","coverage_receipt_path","ledger_snapshot_path","source_index_path","toolchain_path"}}
 bank.update({key:zero for key in {"all_even_manifest_sha256","capacity_inventory_sha256","compact_universe_sha256",
  "complement_manifest_sha256","coverage_receipt_sha256","ledger_snapshot_sha256","selected_ledger_identity_sha256",
  "source_index_sha256","toolchain_sha256"}})
 bank.update({"coverage_terminal_counts":MOD.TERMINAL_COUNTS,"leaf_count":13351,"materializer_sha256":MOD.BANK_PRODUCER_SHA256,
  "materializer_source":MOD.BANK_PRODUCER,"payload_identity_sha256":payload_identity,"payload_index_path":str(payload_path),
  "payload_index_sha256":MOD.sha(payload_path),"profile_counts":MOD.PROFILE_COUNTS,"replay_audit_path":str(replay_audit_path),
  "replay_audit_sha256":MOD.sha(replay_audit_path),"s3_bucket":"test","s3_prefix":"test","schema":MOD.BANK_SCHEMA})
 bank.update({"all_even_manifest_path":coverage_inputs["all_even_manifest"],
  "all_even_manifest_sha256":coverage_inputs["all_even_manifest_sha256"],
  "compact_universe_path":coverage_inputs["compact_inventory"],"compact_universe_sha256":coverage_inputs["compact_inventory_sha256"],
  "complement_manifest_path":coverage_inputs["complement_manifest"],
  "complement_manifest_sha256":coverage_inputs["complement_manifest_sha256"],
  "coverage_receipt_path":str(coverage_path),"coverage_receipt_sha256":MOD.sha(coverage_path)})
 bank.update({"capacity_inventory_path":str(capacity_inventory),"capacity_inventory_sha256":MOD.sha(capacity_inventory),
  "ledger_snapshot_path":str(ledger_receipt_path),"ledger_snapshot_sha256":MOD.sha(ledger_receipt_path),
  "selected_ledger_identity_sha256":selected_identity,"source_index_path":str(source_index),
  "source_index_sha256":MOD.sha(source_index),"toolchain_path":str(bank_tool_path),"toolchain_sha256":MOD.sha(bank_tool_path)})
 bank_path=Path(post["bank_receipt_path"]); bank_path.write_bytes(MOD.canonical(bank)); post["bank_receipt_sha256"]=MOD.sha(bank_path)
 reindex_output=bank_root/"capacity-index.tsv"; reindex_output.write_bytes(source_index.read_bytes())
 reindex={"capacity_total":13351,"dropped_outside_capacity_tags":[],"emitted_rows":13351,
  "indexes":[{"path":str(source_index),"sha256":MOD.sha(source_index)}],"inventory":str(capacity_inventory),
  "inventory_sha256":MOD.sha(capacity_inventory),"output":str(reindex_output),"output_sha256":MOD.sha(reindex_output),
  "require_complete":True,"schema":MOD.REINDEX_SCHEMA}
 reindex_path=Path(post["capacity_reindex_receipt_path"])
 reindex_path.write_text(json.dumps(reindex,indent=2,sort_keys=True)+"\n"); post["capacity_reindex_receipt_sha256"]=MOD.sha(reindex_path)
 aggregate_root=repo/"proofs/Proofs/Generated/H1V2Aggregate"; aggregate_root.mkdir(parents=True)
 aggregate_rows=AGG.read_index(reindex_output)
 AGG.write_hierarchy(aggregate_rows,aggregate_root,"Proofs.Generated.H1V2Certificates",
  "Proofs.Generated.H1V2Aggregate",128,
  inventory_identity={"bytes":capacity_inventory.stat().st_size,"path":str(capacity_inventory),"sha256":MOD.sha(capacity_inventory)},
  index_identity={"bytes":reindex_output.stat().st_size,"path":str(reindex_output),"sha256":MOD.sha(reindex_output)})
 layout_path=aggregate_root/"aggregate-layout.json"; layout=json.loads(layout_path.read_text())
 project_by_path={item["path"]:item for item in axiom["project_cone_source_identities"]}
 endpoint_source=repo/MOD.SOURCE; endpoint_project=project_by_path[MOD.SOURCE]
 endpoint_project["bytes"]=endpoint_source.stat().st_size; endpoint_project["sha256"]=MOD.sha(endpoint_source)
 evidence["adapter_source_identity"]={"blob_oid":endpoint_project["blob_oid"],"bytes":endpoint_source.stat().st_size,
  "repo_path":MOD.SOURCE,"sha256":MOD.sha(endpoint_source)}
 post["endpoint_source_sha256"]=MOD.sha(endpoint_source); cold["endpoint_source_sha256"]=MOD.sha(endpoint_source)
 for record in layout["modules"]:
  text="proofs/"+"/".join(record["module"].split("."))+".lean"; source=repo/text
  axiom["project_cone_source_identities"].append({"blob_oid":"e"*40,"bytes":source.stat().st_size,
   "path":text,"sha256":MOD.sha(source)})
 post["aggregate_layout_path"]=str(layout_path)
 post["aggregate_layout_sha256"]=MOD.sha(layout_path)
 evidence["aggregate_layout_source_identity"]={"blob_oid":"e"*40,"bytes":layout_path.stat().st_size,
  "repo_path":layout_path.relative_to(repo).as_posix(),"sha256":MOD.sha(layout_path)}
 axiom["project_cone_source_identities"].append({"blob_oid":"e"*40,"bytes":layout_path.stat().st_size,
  "path":layout_path.relative_to(repo).as_posix(),"sha256":MOD.sha(layout_path)})
 leaf_modules=[]
 for row in evidence["rows"]:
  module=f"Proofs.Generated.H1V2Certificates.Erdos85H1V2CertP{row['profile']}I{row['capacity_local_index']:05d}"
  repo_path="proofs/"+"/".join(module.split("."))+".lean"; path=repo/repo_path; path.parent.mkdir(parents=True,exist_ok=True)
  theorem=f"h1V2P{row['profile']}I{row['capacity_local_index']:05d}Checked"
  path.write_text(f"theorem {theorem} : True := by trivial\n"); leaf_sha=MOD.sha(path)
  row.update({"leaf_blob_oid":"d"*40,"leaf_repo_path":repo_path,"leaf_source_bytes":path.stat().st_size,
              "leaf_source_sha256":leaf_sha})
  axiom["project_cone_source_identities"].append({"blob_oid":"d"*40,"bytes":path.stat().st_size,
   "path":repo_path,"sha256":leaf_sha})
  leaf_modules.append({"local_index":row["capacity_local_index"],"orbit":row["tag"],
   "packed_lrat_sha256":row["packed_sha256"],"profile":row["profile"],"source_bytes":path.stat().st_size,
   "source_module":module,"source_path":str(path),"source_sha256":leaf_sha})
 for name in ("filter_h1_capacity_inventory.py","encode_h1_v2_binary_lrat.py","compress_h1_v2_binary_lrat.py"):
  text="research/problems/erdos-85-wip-01/sat49/"+name; path=repo/text
  axiom["project_cone_source_identities"].append({"blob_oid":"f"*40,"bytes":path.stat().st_size,
   "path":text,"sha256":MOD.sha(path)})
 project_paths=[item["path"] for item in axiom["project_cone_source_identities"]]
 project_oids=[item["blob_oid"] for item in axiom["project_cone_source_identities"]]
 for kind,tail in (("project_commit_oids",[f"{axiom['source_commit']}:{p}" for p in project_paths]),
                   ("project_worktree_oids",project_paths)):
  record=axiom["commands"][kind]; record["argv"]=record["argv"][:4 if kind=="project_commit_oids" else 5]+tail
  core={"argv":record["argv"],"cwd":record["cwd"],"environment":{},"kind":kind}
  record["command_identity_sha256"]=__import__("hashlib").sha256(MOD.canonical(core)).hexdigest()
  stdout=axiom_path.parent/record["stdout_path"]; stdout.write_text("\n".join(project_oids)+"\n")
  record["stdout_sha256"]=MOD.sha(stdout); record["stdout_bytes"]=stdout.stat().st_size
 leaf={"capacity_index_sha256":MOD.sha(reindex_output),"leaf_count":13351,"modules":leaf_modules,"schema":MOD.LEAF_SCHEMA}
 leaf_path=Path(post["leaf_module_index_path"]); leaf_path.write_bytes(MOD.canonical(leaf)); post["leaf_module_index_sha256"]=MOD.sha(leaf_path)
 adapter={key:"unused" for key in {"input_top_module",
  "input_top_path","input_top_repo_path","input_top_theorem","output_path"}}
 adapter.update({key:zero for key in {"aggregate_sources_identity_sha256","capacity_index_sha256","generator_sha256",
  "input_top_sha256"}})
 adapter.update({"aggregate_layout_path":str(layout_path),"aggregate_layout_sha256":post["aggregate_layout_sha256"],
  "aggregate_source_root":str(aggregate_root),
  "capacity_index_path":str(reindex_output),"capacity_index_sha256":MOD.sha(reindex_output),
  "capacity_reindex_receipt_path":str(reindex_path),"capacity_reindex_receipt_sha256":post["capacity_reindex_receipt_sha256"],
  "generator_source":MOD.ADAPTER_PRODUCER,"generator_sha256":MOD.ADAPTER_PRODUCER_SHA256,
  "leaf_count":13351,"leaf_module_index_path":str(leaf_path),"leaf_module_index_sha256":post["leaf_module_index_sha256"],
  "output_bytes":len(sources[MOD.SOURCE]),"output_sha256":post["endpoint_source_sha256"],"output_source_module":MOD.MODULE,
  "output_theorem":MOD.THEOREM,"repo":str(repo),"schema":MOD.ADAPTER_SCHEMA})
 top=next(row for row in layout["modules"] if row["kind"]=="top-bank")
 aggregate_worktree=[]
 for record in layout["modules"]:
  path=repo/("proofs/"+"/".join(record["module"].split("."))+".lean")
  aggregate_worktree.append({"repo_path":path.relative_to(repo).as_posix(),"bytes":path.stat().st_size,
                             "sha256":MOD.sha(path)})
 adapter.update({"aggregate_sources_identity_sha256":__import__("hashlib").sha256(MOD.canonical(aggregate_worktree)).hexdigest(),
  "input_top_module":top["module"],"input_top_path":str(aggregate_root/top["file"]),
  "input_top_repo_path":(aggregate_root/top["file"]).relative_to(repo).as_posix(),"input_top_sha256":top["source_sha256"],
  "input_top_theorem":top["theorem"],"output_path":str(repo/MOD.SOURCE),"output_bytes":(repo/MOD.SOURCE).stat().st_size})
 adapter_path=Path(post["adapter_receipt_path"]); adapter_path.write_bytes(MOD.canonical(adapter)); post["adapter_receipt_sha256"]=MOD.sha(adapter_path)
 project_by_path={item["path"]:item for item in axiom["project_cone_source_identities"]}
 leaf_ids=[{"blob_oid":row["leaf_blob_oid"],"bytes":row["leaf_source_bytes"],"repo_path":row["leaf_repo_path"],
            "sha256":row["leaf_source_sha256"]} for row in evidence["rows"]]
 aggregate_ids=[evidence["aggregate_layout_source_identity"]]
 for record in layout["modules"]:
  text="proofs/"+"/".join(record["module"].split("."))+".lean"; item=project_by_path[text]
  aggregate_ids.append({"blob_oid":item["blob_oid"],"bytes":item["bytes"],"repo_path":text,"sha256":item["sha256"]})
 evidence["leaf_tree_identity_sha256"]=__import__("hashlib").sha256(MOD.canonical(leaf_ids)).hexdigest()
 evidence["aggregate_tree_identity_sha256"]=__import__("hashlib").sha256(MOD.canonical(aggregate_ids)).hexdigest()
 generated=__import__("hashlib").sha256(MOD.canonical([*leaf_ids,*aggregate_ids,evidence["adapter_source_identity"]])).hexdigest()
 evidence["generated_tree_identity_sha256"]=generated; post["generated_tree_identity_sha256"]=generated
 cold["generated_tree_identity_sha256"]=generated
 compiled_by_build={row["build_path"]:row for row in cold["retained_generated_artifacts"]}
 for module in (MOD.MODULE,"Proofs.Generated.H1","Proofs.Generated.Aggregate","Proofs.Generated.Leaf"):
  for suffix in (".olean",".ilean"):
   build=".lake/build/lib/lean/"+"/".join(module.split("."))+suffix
   if build in compiled_by_build: continue
   relative="artifacts/generated/"+"/".join(module.split("."))+suffix
   path=cold_path.parent/relative; path.parent.mkdir(parents=True,exist_ok=True); path.write_bytes((module+suffix+"\n").encode())
   cold["retained_generated_artifacts"].append({"artifact_path":relative,"build_path":build,
    "bytes":path.stat().st_size,"sha256":MOD.sha(path)})
 cold["retained_generated_artifacts"].sort(key=lambda row:row["build_path"])
 evidence_path.write_bytes(MOD.canonical(evidence)); post["evidence_sha256"]=MOD.sha(evidence_path)
 post["producer_path"]=str(repo/MOD.POST_PRODUCER); post_path.write_bytes(MOD.canonical(post))
 cold["post_module_receipt_sha256"]=MOD.sha(post_path); cold["producer_path"]=str(repo/MOD.COLD_PRODUCER)
 cold_path.write_bytes(MOD.canonical(cold)); axiom["cold_receipt_sha256"]=MOD.sha(cold_path)
 axiom["producer_path"]=str(repo/MOD.AXIOM_PRODUCER); axiom_path.write_bytes(MOD.canonical(axiom))
 expected={row["path"]:row["blob_oid"] for row in
           axiom["project_cone_source_identities"]+axiom["audited_source_identities"]}
 state={"bad_worktree":False}
 def runner(kind,argv,cwd):
  if kind=="finalizer_head":
   return {"rc":0,"stdout":b"b"*40+b"\n","stderr":b""}
  if kind in {"finalizer_commit_oid","finalizer_worktree_oid"}:
   return {"rc":0,"stdout":b"c"*40+b"\n","stderr":b""}
  marker="rev-parse" if "rev-parse" in argv else "--"; values=[]
  for token in argv[argv.index(marker)+1:]:
   text=token.split(":",1)[1] if marker=="rev-parse" else token
   values.append(expected.get(text,"a"*40))
  if state["bad_worktree"] and kind=="source_worktree_oids": values[0]="f"*40
  return {"rc":0,"stdout":(("\n".join(values)+"\n").encode()),"stderr":b""}
 args={"repo":repo,"axiom_receipt":axiom_path,"axiom_pin":MOD.sha(axiom_path),
       "output":root/"final","runner":runner}
 return args,state,{"axiom":axiom_path,"repo":repo}

class FinalizeH1WrapperEndpointReceiptTest(unittest.TestCase):
 def test_happy_path_closes_endpoint_and_terminal_chain(self):
  with tempfile.TemporaryDirectory() as directory:
   root=Path(directory); args,_,_=fixture(root); receipt=MOD.build(**args); out=args["output"]
   self.assertEqual(receipt["schema"],MOD.SCHEMA)
   self.assertEqual(receipt["endpoint_identity"]["theorem"],MOD.THEOREM)
   self.assertEqual(receipt["audit_identity"]["status"],"PASS")
   self.assertEqual(receipt["terminal_capacity"]["leaf_count"],13351)
   self.assertEqual(receipt["terminal_capacity"]["profile_counts"],MOD.PROFILE_COUNTS)
   self.assertEqual(receipt["terminal_capacity"]["status"],"PASS")
   self.assertEqual(receipt["terminal_capacity"]["terminal_counts"],MOD.TERMINAL_COUNTS)
   self.assertEqual(receipt["consumer_projection_identity"]["schema"],MOD.PROJECTION_SCHEMA)
   projection=json.loads((out/receipt["consumer_projection_identity"]["path"]).read_text())
   self.assertEqual(set(projection),{"consumer_argument","schema","source_module","source_sha256","theorem"})
   self.assertEqual(projection["source_sha256"],receipt["endpoint_identity"]["source_sha256"])
   self.assertEqual(MOD.sha(out/receipt["endpoint_identity"]["source_path"]),projection["source_sha256"])
   self.assertEqual(receipt["producer_identity"]["path"],MOD.FINAL_PRODUCER)
   self.assertTrue(all(MOD.sha(out/row["path"])==row["sha256"] for row in receipt["artifacts"]))
   with self.assertRaisesRegex(ValueError,"output.*absent"): MOD.build(**args)

 def test_source_nested_and_copy_adversaries_fail(self):
  with tempfile.TemporaryDirectory() as directory:
   root=Path(directory); args,state,_=fixture(root); state["bad_worktree"]=True
   with self.assertRaisesRegex(ValueError,"Git identity"): MOD.build(**args)
  with tempfile.TemporaryDirectory() as directory:
   root=Path(directory); args,_,paths=fixture(root); source=paths["repo"]/MOD.SOURCE
   source.write_text("theorem bad : True := by sorry\n")
   with self.assertRaisesRegex(ValueError,r"hash mismatch|sorry/admit|adapter receipt mismatch"): MOD.build(**args)
  with tempfile.TemporaryDirectory() as directory:
   root=Path(directory); args,_,_=fixture(root); real=MOD.shutil.copyfile
   def corrupt(source,destination):
    result=real(source,destination)
    if str(destination).endswith("evidence/endpoint/Erdos85OrderFortyNineOneHighCertificates.olean"):
     Path(destination).write_bytes(b"corrupt\n")
    return result
   with mock.patch.object(MOD.shutil,"copyfile",side_effect=corrupt):
    with self.assertRaisesRegex(ValueError,"retained evidence"): MOD.build(**args)
  with tempfile.TemporaryDirectory() as directory:
   root=Path(directory); args,_,paths=fixture(root); axiom=json.loads(paths["axiom"].read_text())
   cold_path=Path(axiom["cold_receipt_path"]); cold=json.loads(cold_path.read_text())
   artifact=cold_path.parent/cold["retained_generated_artifacts"][0]["artifact_path"]
   real=artifact.with_suffix(".real"); artifact.rename(real); artifact.symlink_to(real)
   with self.assertRaisesRegex(ValueError,"compiled artifact"): MOD.build(**args)

 def test_toctou_extra_special_and_retry_fail_closed(self):
  callbacks=("extra","directory","fifo","hardlink","input","replace")
  for kind in callbacks:
   with self.subTest(kind=kind),tempfile.TemporaryDirectory() as directory:
    root=Path(directory); args,_,paths=fixture(root)
    original=paths["axiom"].read_bytes()
    def mutate(kind=kind):
     if kind=="input": paths["axiom"].write_bytes(original+b"x")
     elif kind=="replace":
      replacement=paths["axiom"].with_suffix(".replacement"); replacement.write_bytes(original); os.replace(replacement,paths["axiom"])
     else:
      matches=list(root.glob(".h1-wrapper-final-stage.*/publication")); assert len(matches)==1
      if kind=="hardlink":
       files=[path for path in matches[0].rglob("*") if path.is_file()]; groups={}
       for path in files: groups.setdefault((path.stat().st_size,MOD.sha(path)),[]).append(path)
       source,target=next(paths[:2] for paths in groups.values() if len(paths)>=2)
       target.unlink(); os.link(source,target); return
      target=matches[0]/("late.fifo" if kind=="fifo" else "late.dir" if kind=="directory" else "late.bin")
      if kind=="fifo": os.mkfifo(target)
      elif kind=="directory": target.mkdir()
      else: target.write_bytes(b"late\n")
    args["before_receipt"]=mutate
    with self.assertRaisesRegex(ValueError,r"input drift|input replacement|evidence tree|final evidence"): MOD.build(**args)
    self.assertFalse(args["output"].exists())
  with tempfile.TemporaryDirectory() as directory:
   root=Path(directory); args,_,_=fixture(root)
   def race(): args["output"].mkdir()
   args["before_publish"]=race
   with self.assertRaisesRegex(ValueError,"output appeared before atomic publication"): MOD.build(**args)
   self.assertTrue(args["output"].is_dir()); self.assertEqual(list(args["output"].iterdir()),[])

 def test_missing_audit_core_and_terminal_payload_corruption_fail(self):
  with tempfile.TemporaryDirectory() as directory:
   root=Path(directory); args,_,paths=fixture(root); axiom=json.loads(paths["axiom"].read_text())
   axiom["artifacts"]=[row for row in axiom["artifacts"] if row["path"]!="audit/print-axioms.log"]
   paths["axiom"].write_bytes(MOD.canonical(axiom)); args["axiom_pin"]=MOD.sha(paths["axiom"])
   with self.assertRaisesRegex(ValueError,"artifact set"): MOD.build(**args)
  with tempfile.TemporaryDirectory() as directory:
   root=Path(directory); args,_,paths=fixture(root); axiom=json.loads(paths["axiom"].read_text())
   cold=json.loads(Path(axiom["cold_receipt_path"]).read_text())
   post=json.loads(Path(cold["post_module_receipt_path"]).read_text())
   evidence=json.loads((Path(cold["post_module_receipt_path"]).parent/post["evidence_path"]).read_text())
   replay=Path(post["bank_receipt_path"]).parent/evidence["rows"][0]["replay_evidence_path"]
   replay.write_bytes(replay.read_bytes()+b"corrupt")
   with self.assertRaisesRegex(ValueError,"terminal evidence file hash mismatch"): MOD.build(**args)

 def test_recursive_bank_schema_spoof_fails_even_when_rehashed(self):
  with tempfile.TemporaryDirectory() as directory:
   root=Path(directory); args,_,paths=fixture(root); axiom=json.loads(paths["axiom"].read_text())
   cold_path=Path(axiom["cold_receipt_path"]); cold=json.loads(cold_path.read_text())
   post_path=Path(cold["post_module_receipt_path"]); post=json.loads(post_path.read_text())
   bank_path=Path(post["bank_receipt_path"]); bank=json.loads(bank_path.read_text()); bank["extra"]="spoof"
   bank_path.write_bytes(MOD.canonical(bank)); post["bank_receipt_sha256"]=MOD.sha(bank_path)
   post_path.write_bytes(MOD.canonical(post)); cold["post_module_receipt_sha256"]=MOD.sha(post_path)
   cold_path.write_bytes(MOD.canonical(cold)); axiom["cold_receipt_sha256"]=MOD.sha(cold_path)
   paths["axiom"].write_bytes(MOD.canonical(axiom)); args["axiom_pin"]=MOD.sha(paths["axiom"])
   with self.assertRaisesRegex(ValueError,"payload bank receipt contract mismatch"): MOD.build(**args)
  with tempfile.TemporaryDirectory() as directory:
   root=Path(directory); args,_,paths=fixture(root); axiom=json.loads(paths["axiom"].read_text())
   cold_path=Path(axiom["cold_receipt_path"]); cold=json.loads(cold_path.read_text())
   post_path=Path(cold["post_module_receipt_path"]); post=json.loads(post_path.read_text())
   bank_path=Path(post["bank_receipt_path"]); bank=json.loads(bank_path.read_text())
   coverage_path=Path(bank["coverage_receipt_path"]); coverage=json.loads(coverage_path.read_text())
   coverage["summary"].update({"certified":13350,"fleet_in_flight":1})
   coverage_path.write_bytes(MOD.canonical(coverage)); bank["coverage_receipt_sha256"]=MOD.sha(coverage_path)
   replay_path=Path(bank["replay_audit_path"]); replay=json.loads(replay_path.read_text())
   replay["coverage_receipt_sha256"]=bank["coverage_receipt_sha256"]
   replay_path.write_bytes(MOD.canonical(replay)); bank["replay_audit_sha256"]=MOD.sha(replay_path)
   bank_path.write_bytes(MOD.canonical(bank)); post["bank_receipt_sha256"]=MOD.sha(bank_path)
   post_path.write_bytes(MOD.canonical(post)); cold["post_module_receipt_sha256"]=MOD.sha(post_path)
   cold_path.write_bytes(MOD.canonical(cold)); axiom["cold_receipt_sha256"]=MOD.sha(cold_path)
   paths["axiom"].write_bytes(MOD.canonical(axiom)); args["axiom_pin"]=MOD.sha(paths["axiom"])
   with self.assertRaisesRegex(ValueError,"coverage is not terminal|selected ledger receipt mismatch"): MOD.build(**args)
  with tempfile.TemporaryDirectory() as directory:
   root=Path(directory); args,_,paths=fixture(root); axiom=json.loads(paths["axiom"].read_text())
   cold_path=Path(axiom["cold_receipt_path"]); cold=json.loads(cold_path.read_text())
   post_path=Path(cold["post_module_receipt_path"]); post=json.loads(post_path.read_text())
   bank_path=Path(post["bank_receipt_path"]); bank=json.loads(bank_path.read_text())
   bank["coverage_terminal_counts"]={"certified":13350,"fleet_in_flight":1,"pending":0,"status_total":13351}
   bank_path.write_bytes(MOD.canonical(bank)); post["bank_receipt_sha256"]=MOD.sha(bank_path)
   post_path.write_bytes(MOD.canonical(post)); cold["post_module_receipt_sha256"]=MOD.sha(post_path)
   cold_path.write_bytes(MOD.canonical(cold)); axiom["cold_receipt_sha256"]=MOD.sha(cold_path)
   paths["axiom"].write_bytes(MOD.canonical(axiom)); args["axiom_pin"]=MOD.sha(paths["axiom"])
   with self.assertRaisesRegex(ValueError,"payload bank receipt contract mismatch"): MOD.build(**args)

 def test_semantic_replay_leaf_native_and_command_spoofs_fail(self):
  with tempfile.TemporaryDirectory() as directory:
   root=Path(directory); args,_,paths=fixture(root); axiom=json.loads(paths["axiom"].read_text())
   cold_path=Path(axiom["cold_receipt_path"]); cold=json.loads(cold_path.read_text())
   post_path=Path(cold["post_module_receipt_path"]); post=json.loads(post_path.read_text())
   evidence_path=post_path.parent/post["evidence_path"]; evidence=json.loads(evidence_path.read_text())
   bank_path=Path(post["bank_receipt_path"]); bank=json.loads(bank_path.read_text())
   replay_audit_path=Path(bank["replay_audit_path"]); replay_audit=json.loads(replay_audit_path.read_text())
   replay_path=bank_path.parent/replay_audit["rows"][0]["replay_evidence_path"]
   replay=json.loads(replay_path.read_text()); replay["accepted_marker"]="LRAT accepted: false"
   replay_path.write_bytes(MOD.canonical(replay)); pin=MOD.sha(replay_path)
   evidence["rows"][0]["replay_evidence_sha256"]=pin; replay_audit["rows"][0]["replay_evidence_sha256"]=pin
   replay_audit["replay_evidence_identity_sha256"]=__import__("hashlib").sha256(MOD.canonical(replay_audit["rows"])).hexdigest()
   replay_audit_path.write_bytes(MOD.canonical(replay_audit)); bank["replay_audit_sha256"]=MOD.sha(replay_audit_path)
   bank_path.write_bytes(MOD.canonical(bank)); evidence_path.write_bytes(MOD.canonical(evidence))
   post["bank_receipt_sha256"]=MOD.sha(bank_path); post["evidence_sha256"]=MOD.sha(evidence_path)
   post_path.write_bytes(MOD.canonical(post)); cold["post_module_receipt_sha256"]=MOD.sha(post_path)
   cold_path.write_bytes(MOD.canonical(cold)); axiom["cold_receipt_sha256"]=MOD.sha(cold_path)
   paths["axiom"].write_bytes(MOD.canonical(axiom)); args["axiom_pin"]=MOD.sha(paths["axiom"])
   with self.assertRaisesRegex(ValueError,"replay evidence contract mismatch"): MOD.build(**args)
  with tempfile.TemporaryDirectory() as directory:
   root=Path(directory); args,_,paths=fixture(root); axiom=json.loads(paths["axiom"].read_text())
   cold_path=Path(axiom["cold_receipt_path"]); cold=json.loads(cold_path.read_text())
   post_path=Path(cold["post_module_receipt_path"]); post=json.loads(post_path.read_text())
   bank_path=Path(post["bank_receipt_path"]); bank=json.loads(bank_path.read_text())
   replay_audit_path=Path(bank["replay_audit_path"]); replay_audit=json.loads(replay_audit_path.read_text())
   replay_audit["rows"][0]["s3_key"]="forged"
   replay_audit["replay_evidence_identity_sha256"]=__import__("hashlib").sha256(MOD.canonical(replay_audit["rows"])).hexdigest()
   replay_audit_path.write_bytes(MOD.canonical(replay_audit)); bank["replay_audit_sha256"]=MOD.sha(replay_audit_path)
   bank_path.write_bytes(MOD.canonical(bank)); post["bank_receipt_sha256"]=MOD.sha(bank_path)
   post_path.write_bytes(MOD.canonical(post)); cold["post_module_receipt_sha256"]=MOD.sha(post_path)
   cold_path.write_bytes(MOD.canonical(cold)); axiom["cold_receipt_sha256"]=MOD.sha(cold_path)
   paths["axiom"].write_bytes(MOD.canonical(axiom)); args["axiom_pin"]=MOD.sha(paths["axiom"])
   with self.assertRaisesRegex(ValueError,"payload/replay/evidence identity mixing"): MOD.build(**args)
  with tempfile.TemporaryDirectory() as directory:
   root=Path(directory); args,_,paths=fixture(root); axiom=json.loads(paths["axiom"].read_text())
   cold_path=Path(axiom["cold_receipt_path"]); cold=json.loads(cold_path.read_text())
   post_path=Path(cold["post_module_receipt_path"]); post=json.loads(post_path.read_text())
   leaf_path=Path(post["leaf_module_index_path"]); leaf=json.loads(leaf_path.read_text()); leaf["modules"][0]["source_module"]="Proofs.Forged"
   leaf_path.write_bytes(MOD.canonical(leaf)); post["leaf_module_index_sha256"]=MOD.sha(leaf_path)
   adapter_path=Path(post["adapter_receipt_path"]); adapter=json.loads(adapter_path.read_text())
   adapter["leaf_module_index_sha256"]=post["leaf_module_index_sha256"]
   adapter_path.write_bytes(MOD.canonical(adapter)); post["adapter_receipt_sha256"]=MOD.sha(adapter_path)
   post_path.write_bytes(MOD.canonical(post)); cold["post_module_receipt_sha256"]=MOD.sha(post_path)
   cold_path.write_bytes(MOD.canonical(cold)); axiom["cold_receipt_sha256"]=MOD.sha(cold_path)
   paths["axiom"].write_bytes(MOD.canonical(axiom)); args["axiom_pin"]=MOD.sha(paths["axiom"])
   with self.assertRaisesRegex(ValueError,"leaf module/evidence mismatch"): MOD.build(**args)
  with tempfile.TemporaryDirectory() as directory:
   root=Path(directory); args,_,paths=fixture(root); axiom=json.loads(paths["axiom"].read_text())
   artifact=next(row for row in axiom["artifacts"] if row["path"]=="audit/dependency-cone.json")
   cone_path=paths["axiom"].parent/artifact["path"]; cone=json.loads(cone_path.read_text())
   cone["theorems"][0]["transitive_axioms"].append("Foreign.axiom"); cone["theorems"][0]["transitive_axioms"].sort()
   cone_path.write_text(json.dumps(cone,indent=2)+"\n"); artifact["sha256"]=MOD.sha(cone_path); artifact["bytes"]=cone_path.stat().st_size
   audit_artifact=next(row for row in axiom["artifacts"] if row["path"]=="audit/audit-receipt.json")
   audit_path=paths["axiom"].parent/audit_artifact["path"]; audit=json.loads(audit_path.read_text())
   audit["artifacts"]["dependency_cone_sha256"]=artifact["sha256"]; audit_path.write_text(json.dumps(audit,indent=2)+"\n")
   audit_artifact["sha256"]=MOD.sha(audit_path); audit_artifact["bytes"]=audit_path.stat().st_size
   paths["axiom"].write_bytes(MOD.canonical(axiom)); args["axiom_pin"]=MOD.sha(paths["axiom"])
   with self.assertRaisesRegex(ValueError,"forbidden axiom"): MOD.build(**args)
  with tempfile.TemporaryDirectory() as directory:
   root=Path(directory); args,_,paths=fixture(root); axiom=json.loads(paths["axiom"].read_text())
   cold_path=Path(axiom["cold_receipt_path"]); cold=json.loads(cold_path.read_text()); record=cold["commands"]["build"]
   record["argv"]=[*record["argv"],"forged"]
   core={"argv":record["argv"],"cwd":record["cwd"],"environment":{},"kind":"build"}
   record["command_identity_sha256"]=__import__("hashlib").sha256(MOD.canonical(core)).hexdigest()
   cold_path.write_bytes(MOD.canonical(cold)); axiom["cold_receipt_sha256"]=MOD.sha(cold_path)
   paths["axiom"].write_bytes(MOD.canonical(axiom)); args["axiom_pin"]=MOD.sha(paths["axiom"])
   with self.assertRaisesRegex(ValueError,"cold command template expansion mismatch"): MOD.build(**args)

 def test_recursive_tool_bank_layout_tree_and_compiled_spoofs_fail(self):
  with tempfile.TemporaryDirectory() as directory:
   root=Path(directory); args,_,paths=fixture(root); axiom=json.loads(paths["axiom"].read_text())
   cold_path=Path(axiom["cold_receipt_path"]); cold=json.loads(cold_path.read_text())
   tool_path=Path(cold["toolchain_path"]); tool=json.loads(tool_path.read_text()); tool["command_templates"]["build"].append("forged")
   tool_path.write_bytes(MOD.canonical(tool)); cold["toolchain_sha256"]=MOD.sha(tool_path)
   cold_path.write_bytes(MOD.canonical(cold)); axiom["cold_receipt_sha256"]=MOD.sha(cold_path); axiom["toolchain_sha256"]=MOD.sha(tool_path)
   paths["axiom"].write_bytes(MOD.canonical(axiom)); args["axiom_pin"]=MOD.sha(paths["axiom"])
   with self.assertRaisesRegex(ValueError,"toolchain contract mismatch"): MOD.build(**args)
  with tempfile.TemporaryDirectory() as directory:
   root=Path(directory); args,_,paths=fixture(root); axiom=json.loads(paths["axiom"].read_text())
   cold_path=Path(axiom["cold_receipt_path"]); cold=json.loads(cold_path.read_text())
   post_path=Path(cold["post_module_receipt_path"]); post=json.loads(post_path.read_text())
   bank_path=Path(post["bank_receipt_path"]); bank=json.loads(bank_path.read_text())
   index_path=Path(bank["source_index_path"]); lines=index_path.read_text().splitlines(); fields=lines[1].split("\t")
   fields[6]="2"; lines[1]="\t".join(fields); index_path.write_text("\n".join(lines)+"\n")
   bank["source_index_sha256"]=MOD.sha(index_path); bank_path.write_bytes(MOD.canonical(bank))
   post["bank_receipt_sha256"]=MOD.sha(bank_path); post_path.write_bytes(MOD.canonical(post))
   cold["post_module_receipt_sha256"]=MOD.sha(post_path); cold_path.write_bytes(MOD.canonical(cold))
   axiom["cold_receipt_sha256"]=MOD.sha(cold_path); paths["axiom"].write_bytes(MOD.canonical(axiom)); args["axiom_pin"]=MOD.sha(paths["axiom"])
   with self.assertRaisesRegex(ValueError,"bank source index ordering mismatch"): MOD.build(**args)
  with tempfile.TemporaryDirectory() as directory:
   root=Path(directory); args,_,paths=fixture(root); axiom=json.loads(paths["axiom"].read_text())
   cold_path=Path(axiom["cold_receipt_path"]); cold=json.loads(cold_path.read_text())
   post_path=Path(cold["post_module_receipt_path"]); post=json.loads(post_path.read_text())
   bank_path=Path(post["bank_receipt_path"]); bank=json.loads(bank_path.read_text())
   tool_path=Path(bank["toolchain_path"]); tool=json.loads(tool_path.read_text()); tool["command_identity_derivation"]="forged"
   tool_path.write_bytes(MOD.canonical(tool)); bank["toolchain_sha256"]=MOD.sha(tool_path); bank_path.write_bytes(MOD.canonical(bank))
   post["bank_receipt_sha256"]=MOD.sha(bank_path); post_path.write_bytes(MOD.canonical(post))
   cold["post_module_receipt_sha256"]=MOD.sha(post_path); cold_path.write_bytes(MOD.canonical(cold))
   axiom["cold_receipt_sha256"]=MOD.sha(cold_path); paths["axiom"].write_bytes(MOD.canonical(axiom)); args["axiom_pin"]=MOD.sha(paths["axiom"])
   with self.assertRaisesRegex(ValueError,"bank toolchain command contract mismatch"): MOD.build(**args)
  for mutation in ("environment","helper","lz4_version"):
   with self.subTest(bank_tool_mutation=mutation),tempfile.TemporaryDirectory() as directory:
    root=Path(directory); args,_,paths=fixture(root); axiom=json.loads(paths["axiom"].read_text())
    cold_path=Path(axiom["cold_receipt_path"]); cold=json.loads(cold_path.read_text())
    post_path=Path(cold["post_module_receipt_path"]); post=json.loads(post_path.read_text())
    bank_path=Path(post["bank_receipt_path"]); bank=json.loads(bank_path.read_text())
    tool_path=Path(bank["toolchain_path"]); tool=json.loads(tool_path.read_text())
    if mutation=="environment": tool["environments"]["fetch"]["AWS_PROFILE"]="forged"
    elif mutation=="helper": tool["producer_helpers"][0]["sha256"]="f"*64
    else: tool["lz4_version"]=""
    tool_path.write_bytes(MOD.canonical(tool)); bank["toolchain_sha256"]=MOD.sha(tool_path); bank_path.write_bytes(MOD.canonical(bank))
    post["bank_receipt_sha256"]=MOD.sha(bank_path); post_path.write_bytes(MOD.canonical(post))
    cold["post_module_receipt_sha256"]=MOD.sha(post_path); cold_path.write_bytes(MOD.canonical(cold))
    axiom["cold_receipt_sha256"]=MOD.sha(cold_path); paths["axiom"].write_bytes(MOD.canonical(axiom)); args["axiom_pin"]=MOD.sha(paths["axiom"])
    with self.assertRaisesRegex(ValueError,"bank toolchain (command contract|helper identity) mismatch"): MOD.build(**args)
  with tempfile.TemporaryDirectory() as directory:
   root=Path(directory); args,_,paths=fixture(root); axiom=json.loads(paths["axiom"].read_text())
   cold_path=Path(axiom["cold_receipt_path"]); cold=json.loads(cold_path.read_text())
   post_path=Path(cold["post_module_receipt_path"]); post=json.loads(post_path.read_text())
   layout_path=Path(post["aggregate_layout_path"]); layout=json.loads(layout_path.read_text()); layout["top_module"]="Proofs.Forged"
   layout_path.write_text(json.dumps(layout,indent=2,sort_keys=True)+"\n"); post["aggregate_layout_sha256"]=MOD.sha(layout_path)
   adapter_path=Path(post["adapter_receipt_path"]); adapter=json.loads(adapter_path.read_text())
   adapter["aggregate_layout_sha256"]=post["aggregate_layout_sha256"]; adapter_path.write_bytes(MOD.canonical(adapter))
   post["adapter_receipt_sha256"]=MOD.sha(adapter_path); post_path.write_bytes(MOD.canonical(post))
   cold["post_module_receipt_sha256"]=MOD.sha(post_path); cold_path.write_bytes(MOD.canonical(cold))
   axiom["cold_receipt_sha256"]=MOD.sha(cold_path); paths["axiom"].write_bytes(MOD.canonical(axiom)); args["axiom_pin"]=MOD.sha(paths["axiom"])
   with self.assertRaisesRegex(ValueError,"aggregate top module|aggregate manifest"): MOD.build(**args)
  with tempfile.TemporaryDirectory() as directory:
   root=Path(directory); args,_,paths=fixture(root); axiom=json.loads(paths["axiom"].read_text())
   cold_path=Path(axiom["cold_receipt_path"]); cold=json.loads(cold_path.read_text())
   post_path=Path(cold["post_module_receipt_path"]); post=json.loads(post_path.read_text())
   evidence_path=post_path.parent/post["evidence_path"]; evidence=json.loads(evidence_path.read_text())
   evidence["leaf_tree_identity_sha256"]="f"*64; evidence_path.write_bytes(MOD.canonical(evidence)); post["evidence_sha256"]=MOD.sha(evidence_path)
   post_path.write_bytes(MOD.canonical(post)); cold["post_module_receipt_sha256"]=MOD.sha(post_path); cold_path.write_bytes(MOD.canonical(cold))
   axiom["cold_receipt_sha256"]=MOD.sha(cold_path); paths["axiom"].write_bytes(MOD.canonical(axiom)); args["axiom_pin"]=MOD.sha(paths["axiom"])
   with self.assertRaisesRegex(ValueError,"generated source tree identity mismatch"): MOD.build(**args)
  with tempfile.TemporaryDirectory() as directory:
   root=Path(directory); args,_,paths=fixture(root); axiom=json.loads(paths["axiom"].read_text())
   cold_path=Path(axiom["cold_receipt_path"]); cold=json.loads(cold_path.read_text())
   target=next(row for row in cold["retained_generated_artifacts"] if row["build_path"].endswith("H1.ilean"))
   cold["retained_generated_artifacts"].remove(target)
   cold_path.write_bytes(MOD.canonical(cold)); axiom["cold_receipt_sha256"]=MOD.sha(cold_path)
   paths["axiom"].write_bytes(MOD.canonical(axiom)); args["axiom_pin"]=MOD.sha(paths["axiom"])
   with self.assertRaisesRegex(ValueError,"compiled Generated import closure mismatch"): MOD.build(**args)
  with tempfile.TemporaryDirectory() as directory:
   root=Path(directory); args,_,paths=fixture(root); axiom=json.loads(paths["axiom"].read_text())
   cold_path=Path(axiom["cold_receipt_path"]); cold=json.loads(cold_path.read_text())
   original=next(row for row in cold["retained_generated_artifacts"] if row["build_path"].endswith("H1.olean"))
   duplicate=dict(original); duplicate["artifact_path"]="artifacts/generated/duplicate.olean"
   duplicate_path=cold_path.parent/duplicate["artifact_path"]; duplicate_path.parent.mkdir(parents=True,exist_ok=True)
   duplicate_path.write_bytes((cold_path.parent/original["artifact_path"]).read_bytes())
   cold["retained_generated_artifacts"].append(duplicate); cold_path.write_bytes(MOD.canonical(cold))
   axiom["cold_receipt_sha256"]=MOD.sha(cold_path); paths["axiom"].write_bytes(MOD.canonical(axiom)); args["axiom_pin"]=MOD.sha(paths["axiom"])
   with self.assertRaisesRegex(ValueError,"compiled (module/source mapping|build path duplicate)"): MOD.build(**args)

if __name__=="__main__": unittest.main()
