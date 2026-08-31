#!/usr/bin/env python3
"""Audit the authenticated cold-built H1 endpoint dependency cone and axioms."""
from __future__ import annotations
import argparse, hashlib, importlib.util, json, os, re, resource, shutil, subprocess, tempfile, time
from datetime import datetime
from pathlib import Path, PurePosixPath

SCHEMA="erdos85-h1-endpoint-axiom-audit-v1"
COLD_SCHEMA="erdos85-h1-endpoint-cold-build-v1"
CACHE_SCHEMA="erdos85-h1-offline-dependency-cache-v1"
TOOL_SCHEMA="erdos85-h1-endpoint-cold-build-toolchain-v1"
IMAGE="lean4-arm64@sha256:a5ca6c4e3328a1832d5f9b814ab7c1e35616903b3956341962a5b1a96fb6dff6"
MODULE="Proofs.Generated.Erdos85OrderFortyNineOneHighCertificates"
THEOREM="Erdos85.orderFortyNineStratumExcluded_one_of_generatedCertificates"
SOURCE="proofs/Proofs/Generated/Erdos85OrderFortyNineOneHighCertificates.lean"
AUDITOR="scripts/erdos85_audit_dependency_cone.py"
AUDITOR_SHA256="18d1c214488080842f192e91d020e041de5c193eb16694df5f38082dd7aad7d4"
HELPER="proofs/Proofs/Erdos85DependencyConeAudit.lean"
HELPER_SHA256="45a67200c939f65d1d10d6fe32b42a71085e6fcc8172d6621c4283114058c326"
COLD_PRODUCER="research/problems/erdos-85-wip-01/sat49/run_h1_endpoint_cold_build.py"
COLD_PRODUCER_SHA256="b75f853462378a0e08939b45a8d6900ec6742ca15e25fd9f7cb46495f8c921d8"
SNAPSHOT_PRODUCER="research/problems/erdos-85-wip-01/sat49/snapshot_h1_offline_dependency_cache.py"
SNAPSHOT_PRODUCER_SHA256="931a663376508e3937f8b370eafc04e8750d5a413154246dbd1c31364372dd17"
CACHE_RECEIPT_SCHEMA="erdos85-h1-offline-dependency-cache-snapshot-receipt-v1"
CONTROL_PATHS=("proofs/lean-toolchain","proofs/lakefile.toml","proofs/lake-manifest.json")
FOUNDATIONAL={"propext","Classical.choice","Quot.sound"}
NATIVE=re.compile(r".*\._native\.native_decide\.ax_[0-9_]+")
SHA=re.compile(r"[0-9a-f]{64}"); OID=re.compile(r"[0-9a-f]{40}")

def canonical(value):
 return (json.dumps(value,ensure_ascii=True,allow_nan=False,sort_keys=True,separators=(",",":"))+"\n").encode("ascii")
def sha(path):
 digest=hashlib.sha256()
 with path.open("rb") as stream:
  for block in iter(lambda:stream.read(1<<20),b""): digest.update(block)
 return digest.hexdigest()
def safe(path,label,kind="file",absent=False):
 if not path.is_absolute() or path!=path.resolve(strict=False): raise ValueError(f"{label} must be canonical absolute")
 current=path if path.exists() else path.parent
 while True:
  if current.is_symlink(): raise ValueError(f"{label} has symlink ancestry")
  if current==current.parent: break
  current=current.parent
 if absent:
  if path.exists() or path.is_symlink() or not path.parent.is_dir(): raise ValueError(f"{label} must be absent")
 elif kind=="file" and (not path.is_file() or path.is_symlink()): raise ValueError(f"{label} is not regular file")
 elif kind=="dir" and (not path.is_dir() or path.is_symlink()): raise ValueError(f"{label} is not directory")
def require(path,pin,label):
 safe(path,label)
 if SHA.fullmatch(str(pin)) is None or sha(path)!=pin: raise ValueError(f"{label} hash mismatch")
def read_json(path,pin,label,pretty=False):
 require(path,pin,label); raw=path.read_bytes(); value=json.loads(raw)
 expected=(json.dumps(value,indent=2,sort_keys=pretty)+"\n").encode() if pretty else canonical(value)
 if not isinstance(value,dict) or raw!=expected: raise ValueError(f"{label} serialization mismatch")
 return value
def rel(text,label):
 if not isinstance(text,str) or not text or "\\" in text: raise ValueError(f"{label} malformed")
 path=PurePosixPath(text)
 if path.is_absolute() or path.as_posix()!=text or any(p in ("",".","..") for p in path.parts):
  raise ValueError(f"{label} malformed")
 return path
def run(runner,kind,argv,cwd,stdout,stderr):
 result=runner(kind,argv,cwd,{},stdout,stderr)
 fields={"cumulative_children_maxrss_kb","rc","system_ns","user_ns","wall_ns"}
 if (not isinstance(result,dict) or set(result)!=fields or result["rc"]!=0
  or any(type(result[k]) is not int or result[k]<0 for k in fields) or result["wall_ns"]<=0):
  raise ValueError(f"{kind} command failed/malformed")
 safe(stdout,f"{kind} stdout"); safe(stderr,f"{kind} stderr")
 core={"argv":argv,"cwd":str(cwd),"environment":{},"kind":kind}
 return {**core,**result,"command_identity_sha256":hashlib.sha256(canonical(core)).hexdigest(),
  "stdout_path":f"logs/{kind}.stdout","stdout_sha256":sha(stdout),"stdout_bytes":stdout.stat().st_size,
  "stderr_path":f"logs/{kind}.stderr","stderr_sha256":sha(stderr),"stderr_bytes":stderr.stat().st_size}
def audit_argv(runtime,checkout):
 return [str(runtime),"run","--rm","--pull=never","--network=none","--read-only","--cpus=8",
  "--memory=32g","--pids-limit=4096","--tmpfs","/tmp:rw,noexec,nosuid,size=2g",
  "-v",f"{checkout}:/workspace:rw","-w","/workspace",IMAGE,"/usr/bin/python3",AUDITOR,
  "--module",MODULE,"--target",THEOREM,"--proofs-dir","/workspace/proofs",
  "--allowlist","/workspace/proofs/.h1-axiom-allowlist.json","--output-dir","/workspace/.h1-axiom-output"]
def fsync_tree(root):
 for path in root.rglob("*"):
  if path.is_file():
   with path.open("rb") as stream: os.fsync(stream.fileno())
 for path in sorted((p for p in root.rglob("*") if p.is_dir()),key=lambda p:len(p.parts),reverse=True)+[root]:
  fd=os.open(path,os.O_RDONLY)
  try: os.fsync(fd)
  finally: os.close(fd)
def scan_rows(root,base,path_key,suffixes=None):
 safe(root,"scan root",kind="dir"); rows=[]
 for current,dirs,files in os.walk(root,followlinks=False):
  parent=Path(current)
  for name in dirs:
   path=parent/name
   if path.is_symlink() or not path.is_dir(): raise ValueError("scanned tree contains special directory")
  for name in files:
   path=parent/name; safe(path,"scanned tree file")
   relpath=PurePosixPath(path.relative_to(base).as_posix())
   if suffixes is not None and relpath.suffix not in suffixes: continue
   rows.append({path_key:relpath.as_posix(),"bytes":path.stat().st_size,"sha256":sha(path)})
 rows.sort(key=lambda x:x[path_key]); return rows
def container_prefix(runtime,checkout):
 return [str(runtime),"run","--rm","--pull=never","--network=none","--read-only","--cpus=8","--memory=32g",
  "--pids-limit=4096","--tmpfs","/tmp:rw,noexec,nosuid,size=2g","-v",f"{checkout}:/workspace:rw",
  "-w","/workspace",IMAGE]
def module_path(module): return "proofs/"+"/".join(module.split("."))+".lean"
def import_closure(checkout,seeds):
 pending=list(seeds); seen=set()
 while pending:
  module=pending.pop()
  if module in seen: continue
  path=checkout/Path(*PurePosixPath(module_path(module)).parts); safe(path,f"module source {module}")
  seen.add(module)
  for raw in path.read_text(encoding="utf-8").splitlines():
   match=re.fullmatch(r"\s*import\s+(Proofs\.[A-Za-z0-9_'.]+)\s*",raw)
   if match and match.group(1) not in seen: pending.append(match.group(1))
 return sorted(seen)

def build(repo,cold_receipt,cold_pin,output,runner,before_receipt=None):
 producer=Path(__file__).resolve(); safe(repo,"repo",kind="dir"); safe(output,"output",absent=True)
 cold=read_json(cold_receipt,cold_pin,"cold receipt")
 cold_fields={"cache_identity_sha256","cache_manifest_path","cache_manifest_sha256","commands","endpoint_module",
  "endpoint_source_path","endpoint_source_sha256","endpoint_theorem","generated_tree_identity_sha256","image",
  "post_module_receipt_path","post_module_receipt_sha256","producer_path","producer_sha256","resource_policy",
  "review_id","reviewed_control_files","retained_generated_artifacts","schema","source_commit",
  "target_generated_artifact_path","target_olean_build_path","target_olean_bytes","target_olean_path",
  "target_olean_sha256","toolchain_path","toolchain_sha256","cache_snapshot_producer_sha256",
  "cache_snapshot_producer_identity","cache_snapshot_receipt_path","cache_snapshot_receipt_sha256"}
 if (set(cold)!=cold_fields or cold.get("schema")!=COLD_SCHEMA or cold.get("image")!=IMAGE
  or cold.get("endpoint_module")!=MODULE or cold.get("endpoint_theorem")!=THEOREM
  or cold.get("endpoint_source_path")!=SOURCE or OID.fullmatch(str(cold.get("source_commit"))) is None
  or cold.get("producer_path")!=str(Path(__file__).resolve().parent/"run_h1_endpoint_cold_build.py")
  or cold.get("producer_sha256")!=COLD_PRODUCER_SHA256):
  raise ValueError("cold receipt contract mismatch")
 cold_command_fields={"argv","command_identity_sha256","cumulative_children_maxrss_kb","cwd","environment","kind",
  "rc","stderr_bytes","stderr_path","stderr_sha256","stdout_bytes","stdout_path","stdout_sha256","system_ns","user_ns","wall_ns"}
 cold_command_names={"clone","checkout","head","status","control_commit_oids","control_worktree_oids",
  "cache_producer_commit_oid","cache_producer_worktree_oid","tool_hashes","lean_version","lake_version","build","status_after"}
 cold_commands=cold.get("commands")
 if (not isinstance(cold_commands,dict) or set(cold_commands)!=cold_command_names
  or any(not isinstance(record,dict) or set(record)!=cold_command_fields or record.get("kind")!=kind
         or record.get("stdout_path")!=f"logs/{kind}.stdout" or record.get("stderr_path")!=f"logs/{kind}.stderr"
         for kind,record in cold_commands.items())):
  raise ValueError("cold command evidence schema mismatch")
 cache_receipt=Path(cold["cache_snapshot_receipt_path"])
 cache_receipt_value=read_json(cache_receipt,cold["cache_snapshot_receipt_sha256"],"cache snapshot receipt")
 cache_receipt_fields={"cache_manifest_path","cache_manifest_sha256","control_files","entry_count","git_path",
  "git_sha256","package_count","packages","producer_path","producer_sha256","repo","schema","source_commit"}
 if (set(cache_receipt_value)!=cache_receipt_fields or cache_receipt_value.get("schema")!=CACHE_RECEIPT_SCHEMA
  or cache_receipt_value.get("source_commit")!=cold["source_commit"] or cache_receipt_value.get("repo")!=str(repo)
  or cache_receipt_value.get("producer_path")!=str(repo/Path(*PurePosixPath(SNAPSHOT_PRODUCER).parts))
  or cache_receipt_value.get("producer_sha256")!=SNAPSHOT_PRODUCER_SHA256
  or cache_receipt_value.get("cache_manifest_path")!="cache-manifest.json"
  or cache_receipt_value.get("cache_manifest_sha256")!=cold["cache_manifest_sha256"]):
  raise ValueError("cache snapshot receipt contract mismatch")
 snapshot_identity=cold.get("cache_snapshot_producer_identity")
 if (cold.get("cache_snapshot_producer_sha256")!=SNAPSHOT_PRODUCER_SHA256
  or not isinstance(snapshot_identity,dict) or set(snapshot_identity)!={"blob_oid","bytes","path","sha256"}
  or snapshot_identity.get("sha256")!=cache_receipt_value.get("producer_sha256")
  or snapshot_identity.get("path")!=SNAPSHOT_PRODUCER or type(snapshot_identity.get("bytes")) is not int
  or snapshot_identity["bytes"]<=0
  or OID.fullmatch(str(snapshot_identity.get("blob_oid"))) is None):
  raise ValueError("cold cache snapshot producer identity mismatch")
 cache_manifest=cache_receipt.parent/"cache-manifest.json"; cache_pin=cold["cache_manifest_sha256"]
 if cold["cache_manifest_path"]!=str(cache_manifest): raise ValueError("cold/cache snapshot manifest path mismatch")
 toolchain=Path(cold["toolchain_path"]); tool_pin=cold["toolchain_sha256"]
 cache=read_json(cache_manifest,cache_pin,"cache manifest")
 if set(cache)!={"entries","identity_sha256","root","schema"} or cache.get("schema")!=CACHE_SCHEMA \
   or hashlib.sha256(canonical(cache.get("entries"))).hexdigest()!=cache.get("identity_sha256") \
   or cache["identity_sha256"]!=cold["cache_identity_sha256"]:
  raise ValueError("cache manifest contract mismatch")
 cache_root=Path(cache["root"]); safe(cache_root,"cache root",kind="dir")
 if cache_root!=cache_receipt.parent/"cache": raise ValueError("cache root/snapshot receipt mismatch")
 tools=read_json(toolchain,tool_pin,"toolchain")
 cold_producer=Path(cold["producer_path"]); require(cold_producer,COLD_PRODUCER_SHA256,"cold producer")
 spec=importlib.util.spec_from_file_location("h1_banked_cold_contract",cold_producer)
 cold_module=importlib.util.module_from_spec(spec); assert spec.loader is not None; spec.loader.exec_module(cold_module)
 policy={"cpus":8,"memory":"32g","network":"none","pids_limit":4096,"read_only_container":True,
         "tmpfs":"/tmp:rw,noexec,nosuid,size=2g"}
 tool_fields={"command_identity_derivation","command_templates","container_runtime_path","container_runtime_sha256",
              "git_path","git_sha256","image","resource_policy","schema"}
 if (set(tools)!=tool_fields or tools.get("schema")!=TOOL_SCHEMA or tools.get("image")!=IMAGE
  or tools.get("resource_policy")!=policy or tools.get("command_templates")!=cold_module.templates()
  or tools.get("command_identity_derivation")!="sha256(canonical-json({argv,cwd,environment,kind}))"):
  raise ValueError("toolchain contract mismatch")
 if cold.get("resource_policy")!=policy: raise ValueError("cold resource policy mismatch")
 git=Path(tools["git_path"]); runtime=Path(tools["container_runtime_path"])
 require(git,tools["git_sha256"],"git"); require(runtime,tools["container_runtime_sha256"],"runtime")
 snapshot_producer=repo/Path(*PurePosixPath(SNAPSHOT_PRODUCER).parts)
 require(snapshot_producer,SNAPSHOT_PRODUCER_SHA256,"snapshot producer")
 if (snapshot_identity["bytes"]!=snapshot_producer.stat().st_size
  or cache_receipt_value["producer_path"]!=str(snapshot_producer)):
  raise ValueError("snapshot producer path/bytes mismatch")
 if (cache_receipt_value.get("git_path")!=str(git) or cache_receipt_value.get("git_sha256")!=tools["git_sha256"]
  or cache_receipt_value.get("control_files")!=cold["reviewed_control_files"]):
  raise ValueError("cache snapshot Git/control crosslink mismatch")
 package_fields={"head","manifest_url","name","normalized_remote","path","rev","source_identity_sha256"}
 packages=cache_receipt_value.get("packages")
 if (not isinstance(packages,list) or cache_receipt_value.get("package_count")!=len(packages)
  or any(not isinstance(item,dict) or set(item)!=package_fields for item in packages)):
  raise ValueError("cache snapshot package schema mismatch")
 cold_root=cold_receipt.parent; rows=cold["retained_generated_artifacts"]
 cold_log_pins={}
 cold_clone=cold_commands["clone"]
 cold_checkout=(cold_clone.get("argv") or [None])[-1]; cold_stage=cold_clone.get("cwd")
 cold_stage_path=Path(str(cold_stage)); cold_checkout_path=Path(str(cold_checkout))
 if (not cold_stage_path.is_absolute() or cold_stage_path!=cold_stage_path.resolve(strict=False)
  or cold_stage_path.parent!=cold_root.parent or not cold_stage_path.name.startswith(".h1-cold-build-stage.")
  or not cold_checkout_path.is_absolute() or cold_checkout_path!=cold_checkout_path.resolve(strict=False)
  or cold_checkout_path!=cold_stage_path/"checkout"):
  raise ValueError("cold stage/checkout path identity mismatch")
 template_values={"git":str(git),"runtime":str(runtime),"repo":str(repo),"checkout":cold_checkout,
  "commit":cold["source_commit"],"image":IMAGE}
 for kind,record in cold_commands.items():
  core={"argv":record.get("argv"),"cwd":record.get("cwd"),"environment":record.get("environment"),"kind":kind}
  expected_argv=cold_module.expand(cold_module.templates()[kind],template_values)
  if (record.get("argv")!=expected_argv or record.get("cwd")!=cold_stage or record.get("environment")!={}
   or record.get("command_identity_sha256")!=hashlib.sha256(canonical(core)).hexdigest()
   or record.get("rc")!=0 or any(type(record.get(k)) is not int or record[k]<0 for k in
      ("cumulative_children_maxrss_kb","rc","system_ns","user_ns","wall_ns","stdout_bytes","stderr_bytes"))
   or record.get("wall_ns",0)<=0 or record.get("cumulative_children_maxrss_kb",0)<=0):
   raise ValueError("cold command evidence identity mismatch")
  for stream in ("stdout","stderr"):
   log=cold_root/record[f"{stream}_path"]
   require(log,record[f"{stream}_sha256"],f"cold {kind} {stream} log")
   if log.stat().st_size!=record[f"{stream}_bytes"]: raise ValueError("cold command log bytes mismatch")
   cold_log_pins[str(log)]=record[f"{stream}_sha256"]
 row_fields={"artifact_path","build_path","bytes","sha256"}
 if (not isinstance(rows,list) or not rows or any(not isinstance(x,dict) or set(x)!=row_fields for x in rows)
  or [x["build_path"] for x in rows]!=sorted(x["build_path"] for x in rows)):
  raise ValueError("retained generated cone schema mismatch")
 endpoint_rows=[row for row in rows if row.get("build_path")==cold.get("target_olean_build_path")]
 if (len(endpoint_rows)!=1 or cold.get("target_generated_artifact_path")!=endpoint_rows[0]["artifact_path"]
  or cold.get("target_olean_sha256")!=endpoint_rows[0]["sha256"]
  or cold.get("target_olean_bytes")!=endpoint_rows[0]["bytes"]):
  raise ValueError("cold endpoint/generated artifact crosslink mismatch")
 legacy_target=cold_root/Path(*rel(cold["target_olean_path"],"cold target olean path").parts)
 require(legacy_target,cold["target_olean_sha256"],"cold legacy target olean")
 if legacy_target.stat().st_size!=cold["target_olean_bytes"]: raise ValueError("cold target olean bytes mismatch")
 controls=cold.get("reviewed_control_files")
 if (not isinstance(controls,list) or [item.get("path") if isinstance(item,dict) else None for item in controls]!=list(CONTROL_PATHS)
  or any(set(item)!={"blob_oid","bytes","path","sha256"} or OID.fullmatch(str(item["blob_oid"])) is None
         or SHA.fullmatch(str(item["sha256"])) is None or type(item["bytes"]) is not int or item["bytes"]<=0
         for item in controls)):
  raise ValueError("cold control identity contract mismatch")
 generated_modules=[]; build_paths=set(); artifact_paths=set(); input_pins={str(cold_receipt):cold_pin,str(cache_receipt):cold["cache_snapshot_receipt_sha256"],
  str(cache_manifest):cache_pin,str(toolchain):tool_pin,str(cold_producer):COLD_PRODUCER_SHA256,
  str(git):tools["git_sha256"],str(runtime):tools["container_runtime_sha256"],str(producer):sha(producer),
  str(snapshot_producer):SNAPSHOT_PRODUCER_SHA256}
 input_pins.update(cold_log_pins)
 for row in rows:
  build_rel=rel(row["build_path"],"generated build path"); artifact_rel=rel(row["artifact_path"],"generated artifact path")
  expected_artifact=PurePosixPath("artifacts/generated",*build_rel.parts[4:])
  if (build_rel.parts[:6]!=(".lake","build","lib","lean","Proofs","Generated")
   or build_rel.suffix not in (".olean",".ilean") or artifact_rel!=expected_artifact
   or row["build_path"] in build_paths or row["artifact_path"] in artifact_paths
   or type(row["bytes"]) is not int or row["bytes"]<=0 or SHA.fullmatch(str(row["sha256"])) is None):
   raise ValueError("generated row malformed")
  build_paths.add(row["build_path"]); artifact_paths.add(row["artifact_path"])
  source=cold_root/Path(*artifact_rel.parts); require(source,row["sha256"],"retained generated artifact")
  if source.stat().st_size!=row["bytes"]: raise ValueError("retained generated artifact bytes mismatch")
  input_pins[str(source)]=row["sha256"]
  if build_rel.suffix==".olean": generated_modules.append(".".join(build_rel.with_suffix("").parts[4:]))
 if len(set(generated_modules))!=len(generated_modules) or MODULE not in generated_modules: raise ValueError("generated module cone mismatch")
 entries=[]; seen=set(); entry_paths=[]
 for item in cache["entries"]:
  if (not isinstance(item,dict) or set(item)!={"path","bytes","sha256"} or type(item["bytes"]) is not int
   or item["bytes"]<0 or SHA.fullmatch(str(item["sha256"])) is None): raise ValueError("cache entry schema mismatch")
  relative=rel(item["path"],"cache entry")
  if relative.parts[0]!=".lake" or item["path"] in seen: raise ValueError("cache entry path/duplicate mismatch")
  generated_prefix=(".lake","build","lib","lean","Proofs","Generated")
  if relative.parts[:len(generated_prefix)]==generated_prefix and relative.suffix in (".olean",".ilean"):
   raise ValueError("cache contains prebuilt Generated artifact")
  seen.add(item["path"]); entry_paths.append(item["path"])
  path=cache_root/Path(*relative.parts); require(path,item["sha256"],"cache entry")
  if path.stat().st_size!=item["bytes"]: raise ValueError("cache entry bytes mismatch")
  entries.append((path,item)); input_pins[str(path)]=item["sha256"]
 if entry_paths!=sorted(entry_paths): raise ValueError("cache entries not sorted")
 if cache_receipt_value["entry_count"]!=len(entries): raise ValueError("cache snapshot entry count mismatch")
 observed_packages={PurePosixPath(item["path"]).parts[2] for _,item in entries
                    if PurePosixPath(item["path"]).parts[:2]==(".lake","packages")
                    and len(PurePosixPath(item["path"]).parts)>=3}
 if observed_packages!={item["name"] for item in packages}: raise ValueError("cache snapshot package set mismatch")
 for package in packages:
  subset=[item for _,item in entries if PurePosixPath(item["path"]).parts[:3]==(".lake","packages",package["name"])]
  if (not subset or package["source_identity_sha256"]!=hashlib.sha256(canonical(subset)).hexdigest()
   or package["head"]!=package["rev"] or OID.fullmatch(str(package["rev"])) is None):
   raise ValueError("cache snapshot package source identity mismatch")
 stage=Path(tempfile.mkdtemp(prefix=".h1-axiom-audit-",dir=output.parent))
 try:
  checkout=stage/"checkout"; logs=stage/"logs"; publication=stage/"publication"; logs.mkdir(); publication.mkdir()
  records={}
  def invoke(kind,argv,cwd):
   out,err=logs/f"{kind}.stdout",logs/f"{kind}.stderr"; records[kind]=run(runner,kind,argv,cwd,out,err)
  invoke("clone",[str(git),"clone","--no-hardlinks","--no-checkout",str(repo),str(checkout)],stage)
  invoke("checkout",[str(git),"-C",str(checkout),"checkout","--detach",cold["source_commit"]],stage)
  invoke("head",[str(git),"-C",str(checkout),"rev-parse","HEAD"],stage)
  invoke("status",[str(git),"-C",str(checkout),"status","--porcelain=v1","--untracked-files=all"],stage)
  if (logs/"head.stdout").read_text()!=cold["source_commit"]+"\n" or (logs/"status.stdout").read_bytes():
   raise ValueError("audit checkout commit/status mismatch")
  audited_sources=[AUDITOR,HELPER,COLD_PRODUCER,SNAPSHOT_PRODUCER]
  invoke("audit_source_commit_oids",[str(git),"-C",str(checkout),"rev-parse",
    *[f"{cold['source_commit']}:{p}" for p in audited_sources]],stage)
  invoke("audit_source_worktree_oids",[str(git),"-C",str(checkout),"hash-object","--",*audited_sources],stage)
  audit_oids=(logs/"audit_source_commit_oids.stdout").read_text().splitlines()
  if (len(audit_oids)!=len(audited_sources) or audit_oids!=(logs/"audit_source_worktree_oids.stdout").read_text().splitlines()
   or any(OID.fullmatch(x) is None for x in audit_oids)):
   raise ValueError("auditor/helper/cold source Git identity mismatch")
  source_pins={AUDITOR:AUDITOR_SHA256,HELPER:HELPER_SHA256,COLD_PRODUCER:COLD_PRODUCER_SHA256,
               SNAPSHOT_PRODUCER:SNAPSHOT_PRODUCER_SHA256}
  audited_source_identities=[]
  for text,oid in zip(audited_sources,audit_oids,strict=True):
   path=checkout/Path(*PurePosixPath(text).parts); require(path,source_pins[text],f"committed {text}")
   audited_source_identities.append({"blob_oid":oid,"bytes":path.stat().st_size,"path":text,"sha256":source_pins[text]})
  for identity in cold["reviewed_control_files"]:
   if set(identity)!={"blob_oid","bytes","path","sha256"}: raise ValueError("control identity schema mismatch")
   path=checkout/Path(*rel(identity["path"],"control path").parts); require(path,identity["sha256"],"control file")
   if path.stat().st_size!=identity["bytes"]: raise ValueError("control bytes mismatch")
  lake_manifest=json.loads((checkout/"proofs/lake-manifest.json").read_bytes())
  manifest_packages=lake_manifest.get("packages") if isinstance(lake_manifest,dict) else None
  if (not isinstance(manifest_packages,list)
   or [(item.get("name"),item.get("rev"),item.get("url")) for item in manifest_packages]
      !=[(item["name"],item["rev"],item["manifest_url"]) for item in packages]):
   raise ValueError("cache snapshot committed manifest provenance mismatch")
  endpoint_source=checkout/Path(*PurePosixPath(SOURCE).parts)
  require(endpoint_source,cold["endpoint_source_sha256"],"committed endpoint source")
  if re.search(rb"\b(?:sorry|admit)\b",endpoint_source.read_bytes().lower()): raise ValueError("sorry/admit in endpoint source")
  lake_root=checkout/"proofs/.lake"
  if lake_root.exists() or lake_root.is_symlink(): raise ValueError("checkout inherited .lake")
  for source,item in entries:
   destination=checkout/"proofs"/Path(*rel(item["path"],"cache entry").parts); destination.parent.mkdir(parents=True,exist_ok=True)
   shutil.copyfile(source,destination); require(destination,item["sha256"],"restored cache entry")
  for row in rows:
   source=cold_root/Path(*rel(row["artifact_path"],"artifact").parts); destination=checkout/"proofs"/Path(*rel(row["build_path"],"build").parts)
   destination.parent.mkdir(parents=True,exist_ok=True); shutil.copyfile(source,destination); require(destination,row["sha256"],"restored generated artifact")
  expected_cache_rows=[{"path":item["path"],"bytes":item["bytes"],"sha256":item["sha256"]} for _,item in entries]
  expected_cache_rows += [{"path":row["build_path"],"bytes":row["bytes"],"sha256":row["sha256"]} for row in rows]
  expected_cache_rows.sort(key=lambda x:x["path"])
  if scan_rows(checkout/"proofs/.lake",checkout/"proofs","path")!=expected_cache_rows:
   raise ValueError("restored cache exact file set mismatch")
  expected_generated_rows=[{"build_path":row["build_path"],"bytes":row["bytes"],"sha256":row["sha256"]} for row in rows]
  restored_generated=scan_rows(checkout/"proofs/.lake/build/lib/lean/Proofs/Generated",checkout/"proofs","build_path",(".olean",".ilean"))
  if restored_generated!=expected_generated_rows: raise ValueError("restored Generated exact file set mismatch")
  allowed_modules=import_closure(checkout,[MODULE])
  if {module for module in allowed_modules if module.startswith("Proofs.Generated.")}!=set(generated_modules):
   raise ValueError("authenticated Generated cone is not the endpoint import closure")
  module_pattern="(?:"+"|".join(re.escape(x) for x in allowed_modules)+")"
  allow={"schema":1,"allowed_axioms":sorted(FOUNDATIONAL),"native_axiom_regex":NATIVE.pattern,
   "native_families":[{"id":"h1-committed","module_regex":module_pattern,"declaration_regex":"Erdos85\\..*"}]}
  allow_path=checkout/"proofs/.h1-axiom-allowlist.json"; allow_path.write_bytes(canonical(allow))
  audit_output=checkout/".h1-axiom-output"
  prefix=container_prefix(runtime,checkout)
  invoke("tool_hashes",[*prefix[:-1],"--entrypoint","/usr/bin/sha256sum",IMAGE,
    "/usr/bin/python3","/root/.elan/bin/lean","/root/.elan/bin/lake"],stage)
  invoke("python_version",[*prefix,"/usr/bin/python3","--version"],stage)
  invoke("lean_version",[*prefix,"lean","--version"],stage)
  invoke("lake_version",[*prefix,"lake","--version"],stage)
  invoke("audit",audit_argv(runtime,checkout),stage)
  if scan_rows(checkout/"proofs/.lake/build/lib/lean/Proofs/Generated",checkout/"proofs","build_path",(".olean",".ilean"))!=expected_generated_rows:
   raise ValueError("audit changed restored Generated artifact set")
  post_lake_rows=scan_rows(lake_root,checkout/"proofs","path")
  helper_paths={".lake/build/lib/lean/Proofs/Erdos85DependencyConeAudit.olean",
                ".lake/build/lib/lean/Proofs/Erdos85DependencyConeAudit.ilean"}
  pre_by_path={row["path"]:row for row in expected_cache_rows}; post_by_path={row["path"]:row for row in post_lake_rows}
  if (any(post_by_path.get(path)!=row for path,row in pre_by_path.items())
   or any(path not in pre_by_path and path not in helper_paths for path in post_by_path)
   or any(path not in post_by_path for path in pre_by_path)
   or ".lake/build/lib/lean/Proofs/Erdos85DependencyConeAudit.ilean" in post_by_path
      and ".lake/build/lib/lean/Proofs/Erdos85DependencyConeAudit.olean" not in post_by_path):
   raise ValueError("audit changed restored .lake file set")
  tool_lines=(logs/"tool_hashes.stdout").read_text().splitlines()
  cold_tool_record=cold_commands["tool_hashes"]
  cold_tool_log=cold_root/"logs/tool_hashes.stdout"
  require(cold_tool_log,cold_tool_record["stdout_sha256"],"cold tool hash log")
  if cold_tool_log.stat().st_size!=cold_tool_record["stdout_bytes"]: raise ValueError("cold tool hash log bytes mismatch")
  if (not isinstance(cold_tool_record,dict) or len(tool_lines)!=3
   or re.fullmatch(r"[0-9a-f]{64}  /usr/bin/python3",tool_lines[0]) is None
   or re.fullmatch(r"[0-9a-f]{64}  /root/\.elan/bin/lean",tool_lines[1]) is None
   or re.fullmatch(r"[0-9a-f]{64}  /root/\.elan/bin/lake",tool_lines[2]) is None
   or cold_tool_record.get("stdout_sha256")!=sha(cold_tool_log)
   or tool_lines[1:]!=cold_tool_log.read_text().splitlines()):
   raise ValueError("container Python/Lean/Lake tool identity mismatch")
  if not (logs/"python_version.stdout").read_text().startswith("Python 3."):
   raise ValueError("container Python version mismatch")
  for kind in ("lean_version","lake_version"):
   cold_log=cold_root/f"logs/{kind}.stdout"; cold_record=cold_commands[kind]
   require(cold_log,cold_record["stdout_sha256"],f"cold {kind} log")
   if cold_record.get("stdout_sha256")!=sha(cold_log) \
      or (logs/f"{kind}.stdout").read_bytes()!=cold_log.read_bytes():
    raise ValueError(f"container {kind} mismatch")
  receipt_path=audit_output/"audit-receipt.json"; inventory_path=audit_output/"dependency-cone.json"
  safe(receipt_path,"underlying receipt"); safe(inventory_path,"dependency cone")
  audit_receipt=json.loads(receipt_path.read_text()); inventory=json.loads(inventory_path.read_text())
  if (receipt_path.read_bytes()!=(json.dumps(audit_receipt,indent=2)+"\n").encode()
   or inventory_path.read_bytes()!=(json.dumps(inventory,indent=2)+"\n").encode()):
   raise ValueError("underlying audit JSON serialization mismatch")
  receipt_fields={"schema","status","target","theorem_count","literal_theorem_count","private_environment_theorem_count",
   "private_environment_theorems","native_root_count","native_family_counts","errors","artifacts"}
  inventory_fields={"schema","generated_at","git_commit","module","target","allowlist_path","allowlist_sha256",
   "theorem_count","native_roots","theorems"}
  if (set(audit_receipt)!=receipt_fields or audit_receipt.get("schema")!=1 or audit_receipt.get("status")!="PASS"
   or audit_receipt.get("target")!=THEOREM or audit_receipt.get("errors")!=[] or set(inventory)!=inventory_fields
   or inventory.get("schema")!=1 or inventory.get("git_commit")!=cold["source_commit"] or inventory.get("module")!=MODULE
   or inventory.get("target")!=THEOREM or inventory.get("allowlist_path")!="proofs/.h1-axiom-allowlist.json"
   or inventory.get("allowlist_sha256")!=sha(allow_path)
   or inventory.get("theorem_count")!=audit_receipt.get("theorem_count")):
   raise ValueError("underlying audit contract mismatch")
  try: generated_at=datetime.fromisoformat(inventory["generated_at"])
  except (TypeError,ValueError) as error: raise ValueError("underlying audit timestamp malformed") from error
  if generated_at.tzinfo is None: raise ValueError("underlying audit timestamp lacks timezone")
  if (logs/"audit.stderr").read_bytes() or (logs/"audit.stdout").read_bytes()!=receipt_path.read_bytes():
   raise ValueError("underlying audit command output mismatch")
  theorem_fields={"name","module","direct_axioms","transitive_axioms"}; roots=inventory.get("native_roots")
  theorems=inventory.get("theorems")
  if (not isinstance(roots,list) or len(roots)!=audit_receipt.get("native_root_count")
   or not isinstance(theorems,list) or len(theorems)!=inventory["theorem_count"]): raise ValueError("native roots/theorems mismatch")
  theorem_names=[]; cone_modules=set(); theorem_modules={}; transitive_native=set(); direct_native_triples=[]
  for theorem in theorems:
   if (not isinstance(theorem,dict) or set(theorem)!=theorem_fields or not isinstance(theorem["name"],str)
    or theorem["module"] not in allowed_modules or not isinstance(theorem["direct_axioms"],list)
    or not isinstance(theorem["transitive_axioms"],list)
    or theorem["direct_axioms"]!=sorted(set(theorem["direct_axioms"]))
    or theorem["transitive_axioms"]!=sorted(set(theorem["transitive_axioms"]))):
    raise ValueError("theorem inventory schema/order mismatch")
   theorem_names.append(theorem["name"]); cone_modules.add(theorem["module"])
   theorem_modules[theorem["name"]]=theorem["module"]
   direct_native_triples.extend((theorem["name"],theorem["module"],axiom)
                                for axiom in theorem["direct_axioms"] if NATIVE.fullmatch(axiom))
   axioms=set(theorem["transitive_axioms"])
   if not set(theorem["direct_axioms"])<=axioms: raise ValueError("direct/transitive axiom mismatch")
   transitive_native.update(axiom for axiom in axioms if NATIVE.fullmatch(axiom))
   if any(x in axiom for axiom in axioms for x in ("sorryAx","ofReduceBool")) \
      or any(axiom not in FOUNDATIONAL and NATIVE.fullmatch(axiom) is None for axiom in axioms):
    raise ValueError("forbidden/foreign axiom in dependency cone")
  if theorem_names!=sorted(set(theorem_names)): raise ValueError("theorem inventory names not unique/sorted")
  private_names=[name for name in theorem_names if name.startswith("_private.")]
  if (audit_receipt.get("private_environment_theorems")!=private_names
   or audit_receipt.get("private_environment_theorem_count")!=len(private_names)
   or audit_receipt.get("literal_theorem_count")!=len(theorem_names)-len(private_names)):
   raise ValueError("underlying audit theorem counts mismatch")
  root_fields={"theorem","module","axiom","family"}; native_modules=[]
  for root in roots:
   if (not isinstance(root,dict) or set(root)!=root_fields or root.get("family")!="h1-committed"
    or NATIVE.fullmatch(str(root.get("axiom"))) is None): raise ValueError("unattributed native root")
   module=root["module"]
   if module not in cone_modules or theorem_modules.get(root["theorem"])!=module: raise ValueError("foreign native root module")
   native_modules.append(module)
  root_keys=[(root["theorem"],root["module"],root["axiom"]) for root in roots]
  if root_keys!=direct_native_triples or {root["axiom"] for root in roots}!=transitive_native:
   raise ValueError("native root attribution is incomplete/duplicated")
  if audit_receipt.get("native_family_counts")!={"h1-committed":len(roots)}: raise ValueError("native family counts mismatch")
  project_paths=sorted({module_path(module) for module in allowed_modules})
  if project_paths:
   invoke("project_commit_oids",[str(git),"-C",str(checkout),"rev-parse",*[f"{cold['source_commit']}:{p}" for p in project_paths]],stage)
   invoke("project_worktree_oids",[str(git),"-C",str(checkout),"hash-object","--",*project_paths],stage)
   commit_oids=(logs/"project_commit_oids.stdout").read_text().splitlines(); work_oids=(logs/"project_worktree_oids.stdout").read_text().splitlines()
   if len(commit_oids)!=len(project_paths) or commit_oids!=work_oids or any(OID.fullmatch(x) is None for x in commit_oids):
    raise ValueError("project cone source attribution mismatch")
  source_identities=[]
  for path_text,oid in zip(project_paths,commit_oids if project_paths else [],strict=True):
   path=checkout/Path(*PurePosixPath(path_text).parts); safe(path,"native root source")
   if re.search(rb"\b(?:sorry|admit)\b",path.read_bytes().lower()): raise ValueError("sorry/admit in native root source")
   source_identities.append({"blob_oid":oid,"bytes":path.stat().st_size,"path":path_text,"sha256":sha(path)})
  artifacts=audit_receipt["artifacts"]
  artifact_fields={"dependency_cone","dependency_cone_sha256","discovery_log","discovery_log_sha256",
                   "print_axioms_log","print_axioms_log_sha256"}
  if set(artifacts)!=artifact_fields or artifacts["dependency_cone"]!="dependency-cone.json" \
   or artifacts["discovery_log"]!="dependency-cone.log" or artifacts["print_axioms_log"]!="print-axioms.log":
   raise ValueError("underlying artifact schema mismatch")
  expected_audit_files={"audit-receipt.json","dependency-cone.json","dependency-cone.log","print-axioms.log"}
  if {p.name for p in audit_output.iterdir()}!=expected_audit_files or any(not p.is_file() or p.is_symlink() for p in audit_output.iterdir()):
   raise ValueError("underlying audit artifact file set mismatch")
  print_lines=(audit_output/"print-axioms.log").read_text().splitlines()
  delimiters=[line for line in print_lines if line.startswith("ERDOS85_AXIOM_BEGIN\t") or line.startswith("ERDOS85_AXIOM_END\t")]
  literal_names=[name for name in theorem_names if not name.startswith("_private.")]
  expected_delimiters=[item for name in literal_names for item in
                       (f"ERDOS85_AXIOM_BEGIN\t{name}",f"ERDOS85_AXIOM_END\t{name}")]
  if delimiters!=expected_delimiters: raise ValueError("literal print-axioms delimiter mismatch")
  retained=[]
  for name,pin_key in (("audit-receipt.json",None),(artifacts["dependency_cone"],"dependency_cone_sha256"),
    (artifacts["discovery_log"],"discovery_log_sha256"),(artifacts["print_axioms_log"],"print_axioms_log_sha256")):
   source=audit_output/name; safe(source,"underlying audit artifact")
   if pin_key and sha(source)!=artifacts[pin_key]: raise ValueError("underlying artifact hash mismatch")
   destination=publication/"audit"/name; destination.parent.mkdir(exist_ok=True); shutil.copyfile(source,destination)
   retained.append({"bytes":source.stat().st_size,"path":f"audit/{name}","sha256":sha(source)})
  allowlist_sha256=sha(allow_path); allowlist_bytes=allow_path.stat().st_size
  retained_allowlist=publication/"audit/allowlist.json"; shutil.copyfile(allow_path,retained_allowlist)
  require(retained_allowlist,allowlist_sha256,"retained allowlist")
  if retained_allowlist.stat().st_size!=allowlist_bytes: raise ValueError("retained allowlist byte mismatch")
  retained.append({"bytes":allowlist_bytes,"path":"audit/allowlist.json","sha256":allowlist_sha256})
  for path in sorted(helper_paths & set(post_by_path)):
   source=checkout/"proofs"/Path(*PurePosixPath(path).parts)
   identity=post_by_path[path]
   if identity["bytes"]<=0: raise ValueError("audit helper artifact is empty")
   destination=publication/"audit/helper"/source.name; destination.parent.mkdir(parents=True,exist_ok=True)
   shutil.copyfile(source,destination)
   require(destination,identity["sha256"],"retained audit helper")
   if destination.stat().st_size!=identity["bytes"]: raise ValueError("retained audit helper byte mismatch")
   retained.append({"bytes":identity["bytes"],"path":destination.relative_to(publication).as_posix(),"sha256":identity["sha256"]})
  allow_path.unlink(); shutil.rmtree(audit_output)
  invoke("status_after",[str(git),"-C",str(checkout),"status","--porcelain=v1","--untracked-files=all"],stage)
  if (logs/"status_after.stdout").read_bytes(): raise ValueError("audit changed committed source tree")
  for path in logs.iterdir():
   destination=publication/"logs"/path.name; destination.parent.mkdir(exist_ok=True); shutil.copyfile(path,destination)
  final={"allowlist_path":"audit/allowlist.json","allowlist_sha256":allowlist_sha256,
   "artifacts":retained,"audited_source_identities":audited_source_identities,
   "cache_manifest_path":str(cache_manifest),"cache_manifest_sha256":cache_pin,
   "cache_snapshot_receipt_path":str(cache_receipt),"cache_snapshot_receipt_sha256":cold["cache_snapshot_receipt_sha256"],
   "cold_receipt_path":str(cold_receipt),"cold_receipt_sha256":cold_pin,"commands":records,
   "endpoint_module":MODULE,"endpoint_theorem":THEOREM,"foundational_axioms":sorted(FOUNDATIONAL),"image":IMAGE,
   "native_root_count":len(roots),"project_cone_source_identities":source_identities,"producer_path":str(producer),
   "producer_sha256":input_pins[str(producer)],"schema":SCHEMA,"source_commit":cold["source_commit"],
   "theorem_count":inventory["theorem_count"],"toolchain_path":str(toolchain),"toolchain_sha256":tool_pin,
   "tool_identities":{"python_sha256":tool_lines[0].split()[0],"lean_sha256":tool_lines[1].split()[0],
                      "lake_sha256":tool_lines[2].split()[0]}}
  if before_receipt: before_receipt()
  for path,pin in input_pins.items(): require(Path(path),pin,"input drift before receipt")
  for row in retained:
   require(publication/row["path"],row["sha256"],"retained audit artifact")
  for record in records.values():
   for stream in ("stdout","stderr"):
    path=publication/record[f"{stream}_path"]; require(path,record[f"{stream}_sha256"],"retained command log")
    if path.stat().st_size!=record[f"{stream}_bytes"]: raise ValueError("retained command log byte drift")
  for identity in source_identities: require(checkout/identity["path"],identity["sha256"],"native source drift")
  for identity in audited_source_identities: require(checkout/identity["path"],identity["sha256"],"auditor/helper source drift")
  snapshot_checkout=next(identity for identity in audited_source_identities if identity["path"]==SNAPSHOT_PRODUCER)
  if snapshot_checkout!=snapshot_identity: raise ValueError("snapshot producer checkout identity mismatch")
  for _,item in entries:
   path=checkout/"proofs"/Path(*PurePosixPath(item["path"]).parts); require(path,item["sha256"],"restored cache drift")
   if path.stat().st_size!=item["bytes"]: raise ValueError("restored cache byte drift")
  if scan_rows(checkout/"proofs/.lake/build/lib/lean/Proofs/Generated",checkout/"proofs","build_path",(".olean",".ilean"))!=expected_generated_rows:
   raise ValueError("Generated artifact set drift before receipt")
  if scan_rows(lake_root,checkout/"proofs","path")!=post_lake_rows:
   raise ValueError("restored .lake file set drift before receipt")
  expected_publication=sorted(
   [{"path":row["path"],"bytes":row["bytes"],"sha256":row["sha256"]} for row in retained]
   +[{"path":record[f"{stream}_path"],"bytes":record[f"{stream}_bytes"],"sha256":record[f"{stream}_sha256"]}
     for record in records.values() for stream in ("stdout","stderr")],key=lambda row:row["path"])
  if scan_rows(publication,publication,"path")!=expected_publication:
   raise ValueError("publication exact file set mismatch")
  observed_publication_dirs={path.relative_to(publication).as_posix() for path in publication.rglob("*") if path.is_dir()}
  expected_publication_dirs={"audit","logs"}
  if any(row["path"].startswith("audit/helper/") for row in retained): expected_publication_dirs.add("audit/helper")
  if observed_publication_dirs!=expected_publication_dirs:
   raise ValueError("publication exact directory set mismatch")
  (publication/"receipt.json").write_bytes(canonical(final)); fsync_tree(publication)
  if output.exists() or output.is_symlink(): raise ValueError("output appeared")
  publication.rename(output); fd=os.open(output.parent,os.O_RDONLY)
  try: os.fsync(fd)
  finally: os.close(fd)
  return final
 except Exception:
  if stage.exists(): shutil.rmtree(stage)
  raise
 finally:
  if stage.exists(): shutil.rmtree(stage)

def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument("--repo",type=Path,required=True); parser.add_argument("--cold-receipt",type=Path,required=True)
 parser.add_argument("--cold-receipt-sha256",required=True); parser.add_argument("--output",type=Path,required=True); args=parser.parse_args()
 def runner(kind,argv,cwd,environment,stdout,stderr):
  before=resource.getrusage(resource.RUSAGE_CHILDREN); started=time.monotonic_ns()
  with stdout.open("xb") as out,stderr.open("xb") as err:
   result=subprocess.run(argv,cwd=cwd,env=environment,stdout=out,stderr=err)
  after=resource.getrusage(resource.RUSAGE_CHILDREN)
  return {"cumulative_children_maxrss_kb":max(1,int(after.ru_maxrss)),"rc":result.returncode,
   "system_ns":max(0,int((after.ru_stime-before.ru_stime)*1e9)),"user_ns":max(0,int((after.ru_utime-before.ru_utime)*1e9)),
   "wall_ns":max(1,time.monotonic_ns()-started)}
 build(args.repo,args.cold_receipt,args.cold_receipt_sha256,args.output,runner)
if __name__=="__main__": main()
