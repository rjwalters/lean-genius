#!/usr/bin/env python3
from __future__ import annotations

import hashlib, importlib.util, json, os, subprocess, tempfile, unittest
from pathlib import Path
from unittest import mock

HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location("h1_finalizer",HERE/"finalize_h1_leaf_module_evidence.py")
MOD=importlib.util.module_from_spec(spec); assert spec.loader is not None; spec.loader.exec_module(MOD)

def digest(data): return hashlib.sha256(data).hexdigest()
def write_json(path,value,pretty=False):
 path.parent.mkdir(parents=True,exist_ok=True)
 raw=(json.dumps(value,indent=2,sort_keys=True)+"\n").encode() if pretty else MOD.canonical(value)
 path.write_bytes(raw); return digest(raw)
def write(path,data): path.parent.mkdir(parents=True,exist_ok=True); path.write_bytes(data); return digest(data)

def fixture(root):
 root=root.resolve(); repo=root/"repo"; repo.mkdir()
 subprocess.run(["git","init","-q"],cwd=repo,check=True)
 subprocess.run(["git","config","user.email","test@example.invalid"],cwd=repo,check=True)
 subprocess.run(["git","config","user.name","test"],cwd=repo,check=True)
 counts=(1,1,0,0,0); tags=("0123456789abcdef","fedcba9876543210")
 bank=root/"bank"; bank.mkdir(); payload_rows=[]; audit_rows=[]
 capacity=root/"capacity.compact"; write(capacity,b"fixture capacity\n")
 for index,tag in enumerate(tags):
  packed=(f"packed-{tag}").encode(); packed_sha=digest(packed)
  packed_rel=f"packed/{packed_sha[:2]}/{packed_sha}.lrat.lz4p7"; write(bank/packed_rel,packed)
  ledger_rel=f"ledgers/v3/{tag}.line"; ledger_sha=write(bank/ledger_rel,(f"ledger {tag}\n").encode())
  replay_rel=f"replay/{tag}.json"; cnf_sha=digest(("cnf"+tag).encode()); compact_sha=digest(("c"+tag).encode())
  table_rel=f"tables/{tag}.json"; table_sha=write(bank/table_rel,b"[]\n"); commands={}
  for kind in ("cnf_check","cnf_emit","compress","decode","encode","fetch","replay","replay_pin","v2cnf_pin"):
   out_rel=None if kind in ("cnf_emit","decode") else f"logs/{tag}.{kind}.stdout"
   err_rel=f"logs/{tag}.{kind}.stderr"; out_raw=(kind+" out\n").encode(); err_raw=b""
   if out_rel is not None: write(bank/out_rel,out_raw)
   write(bank/err_rel,err_raw)
   core={"argv":[kind],"cwd":"/fixture/work","environment":{},"kind":kind}
   commands[kind]={**core,"command_identity_sha256":digest(MOD.canonical(core)),
    "cumulative_children_maxrss_kb":1,"rc":0,"stderr_bytes":0,"stderr_path":err_rel,
    "stderr_sha256":digest(err_raw),"stdout_bytes":len(out_raw),"stdout_path":out_rel,
    "stdout_sha256":digest(out_raw),"system_ns":1,"user_ns":1,"wall_ns":1}
  replay_sha=write_json(bank/replay_rel,{"accepted_marker":"LRAT accepted: true","commands":commands,
   "cnf_sha256":cnf_sha,"compact_bytes":1,"compact_lrat_sha256":compact_sha,"image":"image@sha256:"+"1"*64,
   "lratreplay_sha256":"2"*64,"schema":MOD.REPLAY_SCHEMA,"table_path":table_rel,
   "table_sha256":table_sha,"tag":tag})
  payload_rows.append({"binary_bytes":1,"binary_lrat_sha256":digest(("b"+tag).encode()),
   "capacity_local_index":0,"cnf_sha256":cnf_sha,"compact_bytes":len(("c"+tag).encode()),"compact_lrat_sha256":compact_sha,
   "gzip_bytes":1,"gzip_sha256":digest(("g"+tag).encode()),"ledger_namespace":"v3",
   "ledger_path":ledger_rel,"ledger_sha256":ledger_sha,"lrat_actions":1,"lz4_frame_bytes":1,
   "lz4_frame_sha256":digest(("f"+tag).encode()),"packed_lz4_bytes":len(packed),
   "packed_lz4_path":packed_rel,"packed_lz4_sha256":packed_sha,"profile":index,"raw_lrat_bytes":1,
   "raw_lrat_sha256":digest(("r"+tag).encode()),"s3_key":f"s3://bucket/prefix/h1/{tag}.compact.lrat.gz",
   "source_cnf_clauses":1,"tag":tag})
  audit_rows.append({"packed_lz4_sha256":packed_sha,"replay_evidence_path":replay_rel,
   "replay_evidence_sha256":replay_sha,"ledger_namespace":"v3","ledger_sha256":ledger_sha,
   "replay_command_identity_sha256":commands["replay"]["command_identity_sha256"],
   "s3_key":payload_rows[-1]["s3_key"],"tag":tag})
 payload=bank/"payload-index.json"; payload_pin=write_json(payload,{"capacity_inventory_sha256":MOD.sha(capacity),
  "profile_counts":list(counts),"rows":payload_rows,"schema":MOD.PAYLOAD_SCHEMA})
 audit=bank/"replay-audit.json"; audit_pin=write_json(audit,{"capacity_inventory_sha256":MOD.sha(capacity),
  "coverage_receipt_sha256":"1"*64,"profile_counts":list(counts),"rows":audit_rows,
  "replay_evidence_identity_sha256":digest(MOD.canonical(audit_rows)),"schema":MOD.AUDIT_SCHEMA})
 source_index=bank/"source-index.tsv"; source_index_pin=write(source_index,b"fixture source index\n")
 toolchain=bank/"toolchain.json"; toolchain_pin=write_json(toolchain,{"fixture":True})
 payload_identity=digest(MOD.canonical([{"path":row["packed_lz4_path"],"sha256":row["packed_lz4_sha256"],
                                        "bytes":row["packed_lz4_bytes"]} for row in payload_rows]))
 bank_fields={"all_even_manifest_path":"/fixture/all","all_even_manifest_sha256":"2"*64,
  "capacity_inventory_path":str(capacity),"capacity_inventory_sha256":MOD.sha(capacity),
  "compact_universe_path":"/fixture/raw","compact_universe_sha256":"3"*64,
  "complement_manifest_path":"/fixture/other","complement_manifest_sha256":"4"*64,
  "coverage_receipt_path":"/fixture/coverage","coverage_receipt_sha256":"1"*64,
  "coverage_terminal_counts":{"certified":2,"fleet_in_flight":0,"pending":0,"status_total":2},
  "leaf_count":2,"ledger_snapshot_path":"/fixture/ledger","ledger_snapshot_sha256":"5"*64,
  "materializer_sha256":"6"*64,"materializer_source":"fixture","payload_identity_sha256":payload_identity,
  "payload_index_path":str(payload),"payload_index_sha256":payload_pin,"profile_counts":list(counts),
  "replay_audit_path":str(audit),"replay_audit_sha256":audit_pin,"s3_bucket":"bucket","s3_prefix":"prefix",
  "schema":MOD.BANK_SCHEMA,"selected_ledger_identity_sha256":"8"*64,"source_index_path":str(source_index),
  "source_index_sha256":source_index_pin,"toolchain_path":str(toolchain),"toolchain_sha256":toolchain_pin}
 bank_receipt=bank/"receipt.json"; bank_pin=write_json(bank_receipt,bank_fields)
 columns=("orbit","profile","localIndex","compact_lrat_sha256","raw_lrat_sha256","cnf_sha256",
  "lrat_actions","source_cnf_clauses","compact_bytes","stub_ready","binary_lrat_sha256","binary_bytes",
  "lz4_frame_sha256","lz4_frame_bytes","packed_lz4_sha256","packed_lz4_bytes")
 index_path=root/"capacity.tsv"; lines=["\t".join(columns)]
 for row in payload_rows:
  values=(row["tag"],MOD.PROFILE_NAMES[row["profile"]],"0",row["compact_lrat_sha256"],row["raw_lrat_sha256"],
   row["cnf_sha256"],"1","1","1","1",row["binary_lrat_sha256"],"1",
   row["lz4_frame_sha256"],"1",row["packed_lz4_sha256"],str(row["packed_lz4_bytes"]))
  lines.append("\t".join(values))
 index_pin=write(index_path,("\n".join(lines)+"\n").encode())
 reindex_source=root/"source.tsv"; reindex_source_pin=write(reindex_source,b"source\n")
 reindex=root/"reindex.json"; reindex_pin=write_json(reindex,{"capacity_total":2,
  "dropped_outside_capacity_tags":[],"emitted_rows":2,"indexes":[{"path":str(reindex_source),"sha256":reindex_source_pin}],
  "inventory":str(capacity),"inventory_sha256":MOD.sha(capacity),"output":str(index_path),
  "output_sha256":index_pin,"require_complete":True,"schema":MOD.REINDEX_SCHEMA},True)
 leaf_modules=[]; materialization_rows=[]; olean_root=root/"oleans"
 for row in payload_rows:
  module=f"Proofs.Generated.LeafP{row['profile']}I00000"; path=repo/"proofs"/Path(*module.split(".")).with_suffix(".lean")
  raw=(f"namespace Erdos85\ntheorem h1V2P{row['profile']}I00000Checked : True := by trivial\nend Erdos85\n").encode()
  source_sha=write(path,raw); leaf_modules.append({"local_index":0,"orbit":row["tag"],
   "packed_lrat_sha256":row["packed_lz4_sha256"],"profile":row["profile"],"source_bytes":len(raw),
   "source_module":module,"source_path":str(path),"source_sha256":source_sha})
  proof=path.parent/f"Erdos85H1V2CertP{row['profile']}I00000.compact.lrat"
  proof_raw=("c"+row["tag"]).encode(); proof_sha=write(proof,proof_raw)
  olean=olean_root/f"Erdos85H1V2CertP{row['profile']}I00000.olean"; olean_raw=("olean "+row["tag"]+"\n").encode()
  olean_sha=write(olean,olean_raw)
  materialization_rows.append({"certificate_gzip_bytes":row["gzip_bytes"],
   "certificate_gzip_sha256":row["gzip_sha256"],"certificate_key":row["s3_key"],
   "compact_lrat_bytes":len(proof_raw),
   "compact_lrat_path":str(proof),"compact_lrat_sha256":proof_sha,"local_index":0,"module":module,
   "olean_artifact_key":f"campaign/oleans/{row['tag']}.olean.zst","olean_bytes":len(olean_raw),
   "olean_path":str(olean),"olean_sha256":olean_sha,"orbit":row["tag"],"profile":row["profile"],
   "recompilable_from_tree":True,"replay_ready_key":f"campaign/replay-ready/{row['tag']}.json",
   "replay_ready_sha256":"a"*64,"receipt_key":f"campaign/receipts/{row['tag']}.json",
   "receipt_sha256":"b"*64,"source_artifact_key":f"campaign/sources/{row['tag']}.lean.zst",
   "source_bytes":len(raw),"source_path":str(path),"source_sha256":source_sha,
   "theorem":f"Erdos85.h1V2P{row['profile']}I00000Checked"})
 leaf_index=root/"leaf-index.json"; leaf_pin=write_json(leaf_index,{"capacity_index_sha256":index_pin,
  "leaf_count":2,"modules":leaf_modules,"schema":MOD.LEAF_SCHEMA})
 materialization=root/"materialization.json"; materialization_pin=write_json(materialization,{
  "capacity_index_sha256":index_pin,"leaf_count":2,"manifest_sha256":"c"*64,
  "module_prefix":"Proofs.Generated","profile_counts":list(counts),"queue_sha256":"d"*64,
  "recompilable_from_tree":True,"rows":materialization_rows,"schema":MOD.MATERIALIZATION_SCHEMA})
 aggregate_module="Proofs.Generated.Aggregate"; aggregate_path=repo/"proofs/Proofs/Generated/Aggregate.lean"
 aggregate_raw=b"import Proofs.Generated.LeafP0I00000\nimport Proofs.Generated.LeafP1I00000\ntheorem aggregate : True := by trivial\n"
 aggregate_sha=write(aggregate_path,aggregate_raw)
 layout=repo/"proofs/Proofs/Generated/aggregate-layout.json"; layout_value={"bank_size":2,
  "inputs":{"index":MOD.file_identity(index_path)},"inventory_contract":{},"leaf_count":2,
  "leaf_members_sha256":"c"*64,"modules":[{"direct_import_count":2,
   "direct_imports":["Proofs.Generated.LeafP0I00000","Proofs.Generated.LeafP1I00000"],
   "file":"Aggregate.lean","kind":"top-bank","members":list(tags),"module":aggregate_module,
   "source_bytes":len(aggregate_raw),"source_sha256":aggregate_sha,"theorem":"Erdos85.aggregate"}],
  "prefixes":{"aggregate_modules":"Proofs.Generated","leaf_modules":"Proofs.Generated"},
  "profile_bank_counts":[1,1,0,0,0],"schema":MOD.LAYOUT_SCHEMA,"top_module":aggregate_module}
 layout_pin=write_json(layout,layout_value,True)
 adapter_path=repo/"proofs/Proofs/Generated/Endpoint.lean"; adapter_raw=b"import Proofs.Generated.Aggregate\ntheorem endpoint : True := by trivial\n"
 adapter_sha=write(adapter_path,adapter_raw)
 aggregate_identity=digest(MOD.canonical([{"repo_path":str(aggregate_path.relative_to(repo)),
                                          "bytes":len(aggregate_raw),"sha256":aggregate_sha}]))
 generator_path=repo/"research/problems/erdos-85-wip-01/sat49/generate_h1_post_aggregate_adapter.py"
 generator_sha=write(generator_path,b"# fixture generator\n")
 adapter_fields={"aggregate_layout_path":str(layout),"aggregate_layout_sha256":layout_pin,
  "aggregate_source_root":str(aggregate_path.parent),"aggregate_sources_identity_sha256":aggregate_identity,
  "capacity_index_path":str(index_path),"capacity_index_sha256":index_pin,
  "capacity_reindex_receipt_path":str(reindex),"capacity_reindex_receipt_sha256":reindex_pin,
  "generator_sha256":generator_sha,
  "generator_source":"research/problems/erdos-85-wip-01/sat49/generate_h1_post_aggregate_adapter.py",
  "input_top_module":aggregate_module,"input_top_path":str(aggregate_path),
  "input_top_repo_path":str(aggregate_path.relative_to(repo)),
  "input_top_sha256":aggregate_sha,"input_top_theorem":"Erdos85.aggregate","leaf_count":2,
  "leaf_module_index_path":str(leaf_index),"leaf_module_index_sha256":leaf_pin,"output_bytes":len(adapter_raw),
  "output_path":str(adapter_path),"output_sha256":adapter_sha,"output_source_module":"Proofs.Generated.Endpoint",
  "output_theorem":"Erdos85.endpoint","repo":str(repo),"schema":MOD.ADAPTER_SCHEMA}
 adapter=root/"adapter.json"; adapter_pin=write_json(adapter,adapter_fields)
 tracked=[*[Path(item["source_path"]).relative_to(repo).as_posix() for item in leaf_modules],
  aggregate_path.relative_to(repo).as_posix(),layout.relative_to(repo).as_posix(),
  adapter_path.relative_to(repo).as_posix(),generator_path.relative_to(repo).as_posix()]
 subprocess.run(["git","add","--",*tracked],cwd=repo,check=True)
 subprocess.run(["git","commit","-qm","fixture"],cwd=repo,check=True)
 commit=subprocess.run(["git","rev-parse","HEAD"],cwd=repo,check=True,text=True,stdout=subprocess.PIPE).stdout.strip()
 args=[repo,commit,"1246",bank_receipt,bank_pin,reindex,reindex_pin,layout,layout_pin,adapter,adapter_pin,
       leaf_index,leaf_pin,materialization,materialization_pin,counts]
 return args,{"repo":repo,"bank":bank,"payload":payload,"adapter_path":adapter_path,
  "leaf":Path(leaf_modules[0]["source_path"]),"materialization":materialization,
  "materialization_rows":materialization_rows}

def run(root,data,output=None):
 evidence,core,pins=MOD.validate(*data[0]); MOD.publish(output or root.resolve()/"out",evidence,core,pins)

class FinalizeH1EvidenceTest(unittest.TestCase):
 def test_committed_tree_is_bound_atomically(self):
  with tempfile.TemporaryDirectory() as directory:
   root=Path(directory); data=fixture(root); run(root,data); out=root/"out"
   receipt=json.loads((out/"receipt.json").read_text()); evidence=json.loads((out/"leaf-evidence.json").read_text())
   self.assertEqual(receipt["schema"],MOD.RECEIPT_SCHEMA); self.assertEqual(evidence["schema"],MOD.EVIDENCE_SCHEMA)
   self.assertEqual(receipt["reviewed_commit"],data[0][1]); self.assertEqual(evidence["review_id"],"1246")
   self.assertEqual(receipt["evidence_path"],"leaf-evidence.json")
   self.assertEqual(receipt["endpoint_source_path"],"proofs/Proofs/Generated/Endpoint.lean")
   self.assertEqual(receipt["endpoint_source_sha256"],MOD.sha(data[1]["adapter_path"]))
   self.assertEqual(receipt["materialization_evidence_sha256"],data[0][14])
   self.assertEqual(len(evidence["rows"]),2); self.assertTrue(all(len(row["leaf_blob_oid"])==40 for row in evidence["rows"]))
   self.assertTrue(all("materialized_olean_sha256" in row and "replay_receipt_sha256" in row
                       and "replay_ready_sha256" in row for row in evidence["rows"]))
   self.assertEqual(receipt["evidence_sha256"],MOD.sha(out/"leaf-evidence.json"))
   for row in data[1]["materialization_rows"]:
    compact=Path(row["compact_lrat_path"]); rel=compact.relative_to(data[1]["repo"]).as_posix()
    self.assertEqual(subprocess.run(["git","cat-file","-e",f"{data[0][1]}:{rel}"],
                                    cwd=data[1]["repo"],stdout=subprocess.DEVNULL,
                                    stderr=subprocess.DEVNULL).returncode,128)
   with self.assertRaisesRegex(ValueError,"output must be an absent"): run(root,data)

 def test_commit_blob_and_crosslink_adversaries_fail(self):
  cases=(
   ("wrong-commit",lambda d:d[0].__setitem__(1,"0"*40),"Git object"),
   ("review",lambda d:d[0].__setitem__(2,"#1246"),"commit/review id"),
   ("leaf-mutation",lambda d:d[1]["leaf"].write_text("changed\n"),"leaf source hash"),
   ("adapter-mutation",lambda d:d[1]["adapter_path"].write_text("changed\n"),"adapter source hash"),
   ("commit-blob",rehashed_uncommitted_leaf,"committed blob/worktree mismatch"),
   ("packed",lambda d:(d[1]["bank"]/json.loads(d[1]["payload"].read_text())["rows"][0]["packed_lz4_path"]).write_bytes(b"bad"),"packed payload hash"),
   ("absolute-packed-path",absolute_packed_path,"packed payload path.*relative POSIX"),
   ("absolute-table-path",absolute_table_path,"v2cnf table path.*relative POSIX"),
   ("log-parent-escape",log_parent_escape,"replay stdout path.*relative POSIX"),
   ("command-log",mutate_command_log,"replay stdout hash mismatch"),
   ("layout-schema",mutate_layout_schema,"aggregate layout module schema"),
   ("payload-crosslink",mutate_payload_crosslink,"ordered bank/module crosslink"),
   ("materialization-order",mutate_materialization_order,"ordered materialization/leaf"),
   ("materialized-olean",mutate_materialized_olean,"materialized olean.*hash"),
   ("materialization-receipt-swap",lambda d:swap_materialization_pair(d,"receipt_key","receipt_sha256"),"artifact key/tag"),
   ("materialization-ready-swap",lambda d:swap_materialization_pair(d,"replay_ready_key","replay_ready_sha256"),"artifact key/tag"),
   ("materialization-certificate-swap",swap_materialized_certificate,"certificate payload crosslink"),
   ("materialization-olean-swap",swap_materialized_olean_pair,"ordered materialization/leaf|olean.*identity|path collision"),
   ("duplicate-olean",duplicate_materialized_olean,"olean path collision|olean.*identity"),
   ("wrong-olean-name",wrong_materialized_olean_name,"compact/olean/receipt identity"),
   ("sorry",commit_sorry,"sorry/admit"))
  for name,mutate,message in cases:
   with self.subTest(name=name),tempfile.TemporaryDirectory() as directory:
    root=Path(directory); data=fixture(root); mutate(data)
    with self.assertRaisesRegex(ValueError,message): run(root,data)

 def test_symlink_toctou_and_nested_mutation_fail(self):
  with tempfile.TemporaryDirectory() as directory:
   root=Path(directory); data=fixture(root); leaf=data[1]["leaf"]; real=leaf.with_suffix(".real"); leaf.rename(real); leaf.symlink_to(real)
   with self.assertRaisesRegex(ValueError,"leaf source.*symlink"): run(root,data)
  with tempfile.TemporaryDirectory() as directory:
   root=Path(directory); data=fixture(root); real_fsync=os.fsync; changed=False
   def mutate(fd):
    nonlocal changed
    real_fsync(fd)
    if not changed:
     changed=True; data[1]["adapter_path"].write_bytes(data[1]["adapter_path"].read_bytes()+b"\n")
   with mock.patch.object(MOD.os,"fsync",side_effect=mutate):
    with self.assertRaisesRegex(ValueError,"input drift"): run(root,data)
   self.assertFalse((root/"out").exists())
  with tempfile.TemporaryDirectory() as directory:
   root=Path(directory); data=fixture(root); real_fsync=os.fsync; changed=False
   def mutate_nested(fd):
    nonlocal changed
    real_fsync(fd); matches=list(root.glob(".h1-committed-evidence-*/publication/leaf-evidence.json"))
    if not changed and matches: changed=True; matches[0].write_bytes(matches[0].read_bytes()+b"\n")
   with mock.patch.object(MOD.os,"fsync",side_effect=mutate_nested):
    with self.assertRaisesRegex(ValueError,"nested output drift"): run(root,data)
   self.assertFalse((root/"out").exists()); run(root,data); self.assertTrue((root/"out/receipt.json").is_file())

def mutate_payload_crosslink(data):
 path=data[1]["payload"]; value=json.loads(path.read_text()); value["rows"][0]["profile"]=1
 pin=write_json(path,value); data[0][4]=pin
 receipt_path=data[0][3]; receipt=json.loads(receipt_path.read_text()); receipt["payload_index_sha256"]=pin
 data[0][4]=write_json(receipt_path,receipt)

def mutate_command_log(data):
 audit=json.loads((data[1]["bank"]/"replay-audit.json").read_text())
 replay=data[1]["bank"]/audit["rows"][0]["replay_evidence_path"]
 value=json.loads(replay.read_text()); log=data[1]["bank"]/value["commands"]["replay"]["stdout_path"]
 log.write_text("spoof\n")

def refresh_payload(data,value):
 path=data[1]["payload"]; pin=write_json(path,value)
 receipt_path=data[0][3]; receipt=json.loads(receipt_path.read_text()); receipt["payload_index_sha256"]=pin
 receipt["payload_identity_sha256"]=digest(MOD.canonical([{"path":row["packed_lz4_path"],
  "sha256":row["packed_lz4_sha256"],"bytes":row["packed_lz4_bytes"]} for row in value["rows"]]))
 data[0][4]=write_json(receipt_path,receipt)

def absolute_packed_path(data):
 value=json.loads(data[1]["payload"].read_text()); relative=value["rows"][0]["packed_lz4_path"]
 value["rows"][0]["packed_lz4_path"]=str(data[1]["bank"]/relative); refresh_payload(data,value)

def refresh_replay(data,mutator):
 bank=data[1]["bank"]; audit_path=bank/"replay-audit.json"; audit=json.loads(audit_path.read_text())
 replay_path=bank/audit["rows"][0]["replay_evidence_path"]; replay=json.loads(replay_path.read_text()); mutator(replay)
 audit["rows"][0]["replay_evidence_sha256"]=write_json(replay_path,replay)
 audit["replay_evidence_identity_sha256"]=digest(MOD.canonical(audit["rows"])); audit_pin=write_json(audit_path,audit)
 receipt_path=data[0][3]; receipt=json.loads(receipt_path.read_text()); receipt["replay_audit_sha256"]=audit_pin
 data[0][4]=write_json(receipt_path,receipt)

def absolute_table_path(data):
 def mutate(replay): replay["table_path"]=str(data[1]["bank"]/replay["table_path"])
 refresh_replay(data,mutate)

def log_parent_escape(data):
 def mutate(replay): replay["commands"]["replay"]["stdout_path"]="../escape.log"
 refresh_replay(data,mutate)

def mutate_layout_schema(data):
 layout=data[0][7]; value=json.loads(layout.read_text()); del value["modules"][0]["direct_imports"]
 pin=write_json(layout,value,True); data[0][8]=pin
 adapter=data[0][9]; av=json.loads(adapter.read_text()); av["aggregate_layout_sha256"]=pin
 data[0][10]=write_json(adapter,av)

def rehashed_uncommitted_leaf(data):
 leaf=data[1]["leaf"]; leaf.write_text("theorem changed : True := by trivial\n")
 leaf_index=data[0][11]; value=json.loads(leaf_index.read_text()); value["modules"][0]["source_sha256"]=MOD.sha(leaf)
 value["modules"][0]["source_bytes"]=leaf.stat().st_size; data[0][12]=write_json(leaf_index,value)
 adapter=data[0][9]; av=json.loads(adapter.read_text()); av["leaf_module_index_sha256"]=data[0][12]
 data[0][10]=write_json(adapter,av)
 refresh_materialization_source(data)

def commit_sorry(data):
 repo=data[1]["repo"]; leaf=data[1]["leaf"]; leaf.write_text("theorem bad : True := by sorry\n")
 leaf_index=data[0][11]; value=json.loads(leaf_index.read_text()); value["modules"][0]["source_sha256"]=MOD.sha(leaf)
 value["modules"][0]["source_bytes"]=leaf.stat().st_size; data[0][12]=write_json(leaf_index,value)
 adapter=data[0][9]; av=json.loads(adapter.read_text()); av["leaf_module_index_sha256"]=data[0][12]
 data[0][10]=write_json(adapter,av)
 refresh_materialization_source(data)
 subprocess.run(["git","add","."],cwd=repo,check=True); subprocess.run(["git","commit","-qm","sorry"],cwd=repo,check=True)
 data[0][1]=subprocess.run(["git","rev-parse","HEAD"],cwd=repo,text=True,stdout=subprocess.PIPE,check=True).stdout.strip()

def refresh_materialization_source(data):
 leaf=data[1]["leaf"]; path=data[0][13]; value=json.loads(path.read_text())
 value["rows"][0]["source_sha256"]=MOD.sha(leaf)
 value["rows"][0]["source_bytes"]=leaf.stat().st_size
 data[0][14]=write_json(path,value)

def mutate_materialization_order(data):
 path=data[0][13]; value=json.loads(path.read_text()); value["rows"].reverse()
 data[0][14]=write_json(path,value)

def mutate_materialized_olean(data):
 Path(data[1]["materialization_rows"][0]["olean_path"]).write_bytes(b"changed\n")

def swap_materialization_pair(data,path_key,sha_key):
 path=data[0][13]; value=json.loads(path.read_text())
 for key in (path_key,sha_key): value["rows"][0][key],value["rows"][1][key]=value["rows"][1][key],value["rows"][0][key]
 data[0][14]=write_json(path,value)

def swap_materialized_olean_pair(data):
 path=data[0][13]; value=json.loads(path.read_text())
 for key in ("olean_path","olean_sha256","olean_bytes"):
  value["rows"][0][key],value["rows"][1][key]=value["rows"][1][key],value["rows"][0][key]
 data[0][14]=write_json(path,value)

def swap_materialized_certificate(data):
 path=data[0][13]; value=json.loads(path.read_text())
 for key in ("certificate_key","certificate_gzip_sha256","certificate_gzip_bytes","compact_lrat_bytes"):
  value["rows"][0][key],value["rows"][1][key]=value["rows"][1][key],value["rows"][0][key]
 data[0][14]=write_json(path,value)

def duplicate_materialized_olean(data):
 path=data[0][13]; value=json.loads(path.read_text())
 for key in ("olean_path","olean_sha256","olean_bytes"):
  value["rows"][1][key]=value["rows"][0][key]
 data[0][14]=write_json(path,value)

def wrong_materialized_olean_name(data):
 path=data[0][13]; value=json.loads(path.read_text()); old=Path(value["rows"][0]["olean_path"])
 wrong=old.with_name("wrong.olean"); old.rename(wrong); value["rows"][0]["olean_path"]=str(wrong)
 data[0][14]=write_json(path,value)

if __name__=="__main__": unittest.main()
