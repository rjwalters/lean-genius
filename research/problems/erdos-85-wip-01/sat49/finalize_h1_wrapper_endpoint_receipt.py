#!/usr/bin/env python3
"""Finalize the authenticated H1 wrapper endpoint evidence chain."""
from __future__ import annotations
import argparse, csv, ctypes, errno, hashlib, importlib.util, json, os, re, shutil, sys, tempfile
from pathlib import Path, PurePosixPath

SCHEMA="erdos85-h1-wrapper-endpoint-receipt-v1"
AXIOM_SCHEMA="erdos85-h1-endpoint-axiom-audit-v1"
COLD_SCHEMA="erdos85-h1-endpoint-cold-build-v1"
CACHE_RECEIPT_SCHEMA="erdos85-h1-offline-dependency-cache-snapshot-receipt-v1"
CACHE_SCHEMA="erdos85-h1-offline-dependency-cache-v1"
TOOL_SCHEMA="erdos85-h1-endpoint-cold-build-toolchain-v1"
POST_SCHEMA="erdos85-h1-leaf-module-evidence-receipt-v1"
EVIDENCE_SCHEMA="erdos85-h1-committed-leaf-evidence-v1"
BANK_SCHEMA="erdos85-h1-capacity-payload-bank-v1"
PAYLOAD_SCHEMA="erdos85-h1-capacity-payload-index-v1"
REPLAY_AUDIT_SCHEMA="erdos85-h1-capacity-replay-audit-v1"
REPLAY_SCHEMA="erdos85-h1-capacity-replay-evidence-v1"
COVERAGE_SCHEMA="erdos85-h1-coverage-audit-snapshot-v1"
BANK_TOOL_SCHEMA="erdos85-h1-capacity-toolchain-v1"
LEDGER_RECEIPT_SCHEMA="erdos85-h1-capacity-selected-ledgers-receipt-v1"
LEDGER_SCHEMA="erdos85-h1-capacity-selected-ledgers-v1"
REINDEX_SCHEMA="erdos85-h1-v2-capacity-reindex-v1"
LAYOUT_SCHEMA="erdos85-h1-v2-aggregate-layout-v1"
ADAPTER_SCHEMA="erdos85-h1-post-aggregate-adapter-generation-v1"
LEAF_SCHEMA="erdos85-h1-leaf-module-index-v1"
AXIOM_PRODUCER="research/problems/erdos-85-wip-01/sat49/audit_h1_endpoint_axioms.py"
AXIOM_PRODUCER_SHA256="0a7942f00d80282906343e6ec5b5197a54a99cf157ac512f7a3239545c470e49"
COLD_PRODUCER="research/problems/erdos-85-wip-01/sat49/run_h1_endpoint_cold_build.py"
COLD_PRODUCER_SHA256="1c94f59bcd9024cbb61555391bbd08f577d7f0790dbcb43d3950bed64c99a1c1"
CACHE_PRODUCER="research/problems/erdos-85-wip-01/sat49/snapshot_h1_offline_dependency_cache.py"
CACHE_PRODUCER_SHA256="931a663376508e3937f8b370eafc04e8750d5a413154246dbd1c31364372dd17"
POST_PRODUCER="research/problems/erdos-85-wip-01/sat49/finalize_h1_leaf_module_evidence.py"
POST_PRODUCER_SHA256="fcdf7e29ac095f1a5a91fc9b115685c8295e858e05cb491fe91f06f6c266c1c4"
FINAL_PRODUCER="research/problems/erdos-85-wip-01/sat49/finalize_h1_wrapper_endpoint_receipt.py"
BANK_PRODUCER="research/problems/erdos-85-wip-01/sat49/materialize_h1_capacity_payload_bank.py"
BANK_PRODUCER_SHA256="fab1267f7fda2108652e6373ac7b2e1fd409ae9290044adec2ab97395ab93cab"
REINDEX_PRODUCER="research/problems/erdos-85-wip-01/sat49/reindex_h1_v2_capacity_certificates.py"
REINDEX_PRODUCER_SHA256="1ff80319931c80aca30d58221355c1504ccf250dccc641f82b9bfc96236c1824"
LAYOUT_PRODUCER="research/problems/erdos-85-wip-01/sat49/generate_h1_v2_lean_aggregate.py"
LAYOUT_PRODUCER_SHA256="27c790f9864ef6d19a59261d1bac3c7d593e66bb668ec6ce8f551bf569db6f80"
ADAPTER_PRODUCER="research/problems/erdos-85-wip-01/sat49/generate_h1_post_aggregate_adapter.py"
ADAPTER_PRODUCER_SHA256="88a9ec3ab7f87463201b61f0afebc274da1dea9f7305b651af39e0138eaec824"
LEDGER_PRODUCER="research/problems/erdos-85-wip-01/sat49/snapshot_h1_capacity_selected_ledgers.py"
LEDGER_PRODUCER_SHA256="ad5b5aafe6be5575eeae1da51a7372aa889b392c23b33d411d71dc07def9a45f"
MODULE="Proofs.Generated.Erdos85OrderFortyNineOneHighCertificates"
THEOREM="Erdos85.orderFortyNineStratumExcluded_one_of_generatedCertificates"
SOURCE="proofs/Proofs/Generated/Erdos85OrderFortyNineOneHighCertificates.lean"
IMAGE="lean4-arm64@sha256:a5ca6c4e3328a1832d5f9b814ab7c1e35616903b3956341962a5b1a96fb6dff6"
FOUNDATIONAL=["Classical.choice","Quot.sound","propext"]
PROFILE_COUNTS=[1485,3617,4717,2693,839]
PROFILE_NAMES=["BBBB","ABBB","AABB","AAAB","AAAA"]
TERMINAL_COUNTS={"certified":13351,"fleet_in_flight":0,"pending":0,"status_total":13351}
RESOURCE_POLICY={"cpus":8,"memory":"32g","network":"none","pids_limit":4096,"read_only_container":True,
 "tmpfs":"/tmp:rw,noexec,nosuid,size=2g"}
PROJECTION_SCHEMA="erdos85-order49-wrapper-provenance-v1"
SHA=re.compile(r"[0-9a-f]{64}"); OID=re.compile(r"[0-9a-f]{40}")
NATIVE=re.compile(r".*\._native\.native_decide\.ax_[0-9_]+")

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
 elif kind=="file" and (not path.is_file() or path.is_symlink()): raise ValueError(f"{label} must be regular file")
 elif kind=="dir" and (not path.is_dir() or path.is_symlink()): raise ValueError(f"{label} must be directory")
def require(path,pin,label):
 safe(path,label)
 if SHA.fullmatch(str(pin)) is None or sha(path)!=pin: raise ValueError(f"{label} hash mismatch")
def read_json(path,pin,label,pretty=False):
 require(path,pin,label); raw=path.read_bytes(); value=json.loads(raw)
 expected=(json.dumps(value,indent=2)+"\n").encode() if pretty else canonical(value)
 if not isinstance(value,dict) or raw!=expected: raise ValueError(f"{label} serialization mismatch")
 return value
def rel(text,label):
 if not isinstance(text,str) or not text or "\\" in text: raise ValueError(f"{label} malformed")
 path=PurePosixPath(text)
 if path.is_absolute() or path.as_posix()!=text or any(x in ("",".","..") for x in path.parts): raise ValueError(f"{label} malformed")
 return path
def normalize_remote(value):
 if not isinstance(value,str): raise ValueError("package remote malformed")
 match=re.fullmatch(r"(?:https://github\.com/|git@github\.com:)([^/]+)/([^/]+?)(?:\.git)?/?",value)
 if match is None: raise ValueError("package remote malformed")
 return f"github.com/{match.group(1).lower()}/{match.group(2).lower()}"
def child(root,text,label):
 path=root/Path(*rel(text,label).parts)
 try: path.relative_to(root)
 except ValueError as error: raise ValueError(f"{label} escapes root") from error
 return path
def run_git(runner,kind,argv,cwd):
 result=runner(kind,argv,cwd)
 if (not isinstance(result,dict) or set(result)!={"rc","stdout","stderr"} or result["rc"]!=0
  or not isinstance(result["stdout"],bytes) or not isinstance(result["stderr"],bytes) or result["stderr"]):
  raise ValueError(f"{kind} Git command failed/malformed")
 return result["stdout"]
def scan(root,base):
 safe(root,"scan root",kind="dir"); rows=[]; directories=[]; inodes=set()
 for current,dirs,files in os.walk(root,followlinks=False):
  parent=Path(current)
  if parent!=base: directories.append(parent.relative_to(base).as_posix())
  for name in dirs:
   path=parent/name
   if path.is_symlink() or not path.is_dir(): raise ValueError("evidence tree contains special directory")
  for name in files:
   path=parent/name; safe(path,"evidence tree file")
   info=os.stat(path,follow_symlinks=False); inode=(info.st_dev,info.st_ino)
   if info.st_nlink!=1 or inode in inodes: raise ValueError("evidence tree contains hardlink alias")
   inodes.add(inode)
   rows.append({"bytes":info.st_size,"path":path.relative_to(base).as_posix(),"sha256":sha(path)})
 rows.sort(key=lambda x:x["path"]); directories.sort(); return rows,directories
def rename_noreplace(source,destination):
 libc=ctypes.CDLL(None,use_errno=True); raw_source=os.fsencode(source); raw_destination=os.fsencode(destination)
 if sys.platform=="darwin" and hasattr(libc,"renamex_np"):
  function=libc.renamex_np; function.argtypes=(ctypes.c_char_p,ctypes.c_char_p,ctypes.c_uint)
  function.restype=ctypes.c_int; rc=function(raw_source,raw_destination,4)  # RENAME_EXCL
 elif sys.platform.startswith("linux") and hasattr(libc,"renameat2"):
  function=libc.renameat2
  function.argtypes=(ctypes.c_int,ctypes.c_char_p,ctypes.c_int,ctypes.c_char_p,ctypes.c_uint)
  function.restype=ctypes.c_int; rc=function(-100,raw_source,-100,raw_destination,1)  # RENAME_NOREPLACE
 else: raise ValueError("atomic no-replace directory publication unavailable")
 if rc!=0:
  code=ctypes.get_errno()
  if code in (errno.EEXIST,errno.ENOTEMPTY): raise ValueError("output appeared before atomic publication")
  raise OSError(code,os.strerror(code),str(destination))
def identity_rows(rows,label):
 seen=set()
 for row in rows:
  if (not isinstance(row,dict) or set(row)!={"bytes","path","sha256"} or type(row["bytes"]) is not int
   or row["bytes"]<0 or SHA.fullmatch(str(row["sha256"])) is None or row["path"] in seen):
   raise ValueError(f"{label} row malformed")
  rel(row["path"],f"{label} path"); seen.add(row["path"])

def validate_commands(value,root,pins,label,expected_kinds):
 fields={"argv","command_identity_sha256","cumulative_children_maxrss_kb","cwd","environment","kind","rc",
  "stderr_bytes","stderr_path","stderr_sha256","stdout_bytes","stdout_path","stdout_sha256","system_ns","user_ns","wall_ns"}
 if not isinstance(value,dict) or set(value)!=expected_kinds: raise ValueError(f"{label} command set mismatch")
 for kind,record in value.items():
  if (not isinstance(kind,str) or not kind or not isinstance(record,dict) or set(record)!=fields
   or record.get("kind")!=kind or not isinstance(record.get("argv"),list)
   or not all(isinstance(token,str) and token for token in record["argv"])
   or not isinstance(record.get("cwd"),str) or not Path(record["cwd"]).is_absolute()
   or record.get("environment")!={} or record.get("rc")!=0
   or any(type(record.get(key)) is not int or record[key]<0 for key in
          ("cumulative_children_maxrss_kb","rc","system_ns","user_ns","wall_ns","stdout_bytes","stderr_bytes"))
   or record["wall_ns"]<=0 or record["cumulative_children_maxrss_kb"]<=0):
   raise ValueError(f"{label} command record malformed")
  core={"argv":record["argv"],"cwd":record["cwd"],"environment":{},"kind":kind}
  if record["command_identity_sha256"]!=hashlib.sha256(canonical(core)).hexdigest():
   raise ValueError(f"{label} command identity mismatch")
  for stream in ("stdout","stderr"):
   if record[f"{stream}_path"]!=f"logs/{kind}.{stream}": raise ValueError(f"{label} command log path mismatch")
   path=child(root,record[f"{stream}_path"],f"{label} command log")
   require(path,record[f"{stream}_sha256"],f"{label} command log")
   if path.stat().st_size!=record[f"{stream}_bytes"]: raise ValueError(f"{label} command log bytes mismatch")
   pins[str(path)]=record[f"{stream}_sha256"]

def build(repo,axiom_receipt,axiom_pin,output,runner,before_receipt=None,before_publish=None):
 producer=Path(__file__).resolve(); safe(repo,"repo",kind="dir"); safe(output,"output",absent=True)
 output_parent_info=os.stat(output.parent,follow_symlinks=False)
 output_parent_pin=(output_parent_info.st_dev,output_parent_info.st_ino)
 axiom=read_json(axiom_receipt,axiom_pin,"axiom receipt")
 axiom_fields={"allowlist_path","allowlist_sha256","artifacts","audited_source_identities","cache_manifest_path",
  "cache_manifest_sha256","cache_snapshot_receipt_path","cache_snapshot_receipt_sha256","cold_receipt_path",
  "cold_receipt_sha256","commands","endpoint_module","endpoint_theorem","foundational_axioms","image",
  "native_root_count","producer_path","producer_sha256","project_cone_source_identities","schema","source_commit",
  "theorem_count","tool_identities","toolchain_path","toolchain_sha256"}
 if (set(axiom)!=axiom_fields or axiom.get("schema")!=AXIOM_SCHEMA or axiom.get("producer_sha256")!=AXIOM_PRODUCER_SHA256
  or axiom.get("producer_path")!=str(repo/AXIOM_PRODUCER) or axiom.get("endpoint_module")!=MODULE
  or axiom.get("endpoint_theorem")!=THEOREM or axiom.get("image")!=IMAGE
  or axiom.get("foundational_axioms")!=FOUNDATIONAL or OID.fullmatch(str(axiom.get("source_commit"))) is None
  or type(axiom.get("theorem_count")) is not int or axiom["theorem_count"]<=0
  or type(axiom.get("native_root_count")) is not int or axiom["native_root_count"]<=0):
  raise ValueError("axiom receipt contract mismatch")
 if axiom.get("allowlist_path")!="audit/allowlist.json": raise ValueError("axiom allowlist path mismatch")
 source_commit=axiom["source_commit"]; axiom_root=axiom_receipt.parent
 artifacts=axiom["artifacts"]; identity_rows(artifacts,"axiom artifact")
 allowed_artifacts={"audit/audit-receipt.json","audit/dependency-cone.json","audit/dependency-cone.log",
  "audit/print-axioms.log","audit/allowlist.json","audit/helper/Erdos85DependencyConeAudit.olean",
  "audit/helper/Erdos85DependencyConeAudit.ilean"}
 artifact_paths={row["path"] for row in artifacts}
 mandatory_artifacts={"audit/audit-receipt.json","audit/dependency-cone.json","audit/dependency-cone.log",
  "audit/print-axioms.log","audit/allowlist.json"}
 helper_olean="audit/helper/Erdos85DependencyConeAudit.olean"
 helper_ilean="audit/helper/Erdos85DependencyConeAudit.ilean"
 if (not isinstance(artifacts,list) or any(row["path"] not in allowed_artifacts for row in artifacts)
  or not mandatory_artifacts.issubset(artifact_paths)
  or (helper_ilean in artifact_paths and helper_olean not in artifact_paths)):
  raise ValueError("axiom artifact set mismatch")
 pins={str(producer):sha(producer),str(axiom_receipt):axiom_pin}
 validate_commands(axiom["commands"],axiom_root,pins,"axiom",{"audit","audit_source_commit_oids",
  "audit_source_worktree_oids","checkout","clone","head","lake_version","lean_version","project_commit_oids",
  "project_worktree_oids","python_version","status","status_after","tool_hashes"})
 for row in artifacts:
  path=child(axiom_root,row["path"],"axiom artifact"); require(path,row["sha256"],"axiom artifact")
  if path.stat().st_size!=row["bytes"]: raise ValueError("axiom artifact byte mismatch")
  pins[str(path)]=row["sha256"]
 if helper_olean in artifact_paths:
  helper_row=next(row for row in artifacts if row["path"]==helper_olean)
  if helper_row["bytes"]<=0: raise ValueError("axiom helper olean must be nonempty")
 if helper_ilean in artifact_paths:
  helper_row=next(row for row in artifacts if row["path"]==helper_ilean)
  if helper_row["bytes"]<=0: raise ValueError("axiom helper ilean must be nonempty")
 audit_row=next(row for row in artifacts if row["path"]=="audit/audit-receipt.json")
 cone_row=next(row for row in artifacts if row["path"]=="audit/dependency-cone.json")
 audit=read_json(child(axiom_root,audit_row["path"],"audit receipt"),audit_row["sha256"],"underlying audit",True)
 cone=read_json(child(axiom_root,cone_row["path"],"cone"),cone_row["sha256"],"dependency cone",True)
 audit_fields={"schema","status","target","theorem_count","literal_theorem_count","private_environment_theorem_count",
  "private_environment_theorems","native_root_count","native_family_counts","errors","artifacts"}
 cone_fields={"schema","generated_at","git_commit","module","target","allowlist_path","allowlist_sha256",
  "theorem_count","native_roots","theorems"}
 if (set(audit)!=audit_fields or set(cone)!=cone_fields or audit.get("schema")!=1 or cone.get("schema")!=1
  or audit.get("status")!="PASS" or audit.get("errors")!=[] or audit.get("target")!=THEOREM
  or audit.get("theorem_count")!=axiom["theorem_count"] or audit.get("native_root_count")!=axiom["native_root_count"]
  or cone.get("git_commit")!=source_commit or cone.get("module")!=MODULE or cone.get("target")!=THEOREM
  or cone.get("theorem_count")!=axiom["theorem_count"] or cone.get("allowlist_path")!="proofs/.h1-axiom-allowlist.json"
  or not isinstance(cone.get("theorems"),list) or not isinstance(cone.get("native_roots"),list)
  or any(type(audit.get(key)) is not int or audit[key]<0 for key in
         ("theorem_count","literal_theorem_count","private_environment_theorem_count","native_root_count"))):
  raise ValueError("underlying audit status/identity mismatch")
 theorem_names=[]; theorem_modules={}; direct_native=[]; transitive_native=set()
 theorem_fields={"name","module","direct_axioms","transitive_axioms"}
 for theorem in cone["theorems"]:
  if (not isinstance(theorem,dict) or set(theorem)!=theorem_fields or not isinstance(theorem["name"],str)
   or not isinstance(theorem["module"],str) or not isinstance(theorem["direct_axioms"],list)
   or not isinstance(theorem["transitive_axioms"],list)
   or theorem["direct_axioms"]!=sorted(set(theorem["direct_axioms"]))
   or theorem["transitive_axioms"]!=sorted(set(theorem["transitive_axioms"]))
   or not set(theorem["direct_axioms"])<=set(theorem["transitive_axioms"])):
   raise ValueError("dependency theorem malformed")
  theorem_names.append(theorem["name"]); theorem_modules[theorem["name"]]=theorem["module"]
  direct_native.extend((theorem["name"],theorem["module"],value) for value in theorem["direct_axioms"]
                       if NATIVE.fullmatch(value))
  for value in theorem.get("transitive_axioms",[]):
   if (not isinstance(value,str) or "sorryAx" in value or "ofReduceBool" in value
    or value not in FOUNDATIONAL and NATIVE.fullmatch(value) is None): raise ValueError("forbidden axiom")
   if NATIVE.fullmatch(value): transitive_native.add(value)
 private_names=[name for name in theorem_names if name.startswith("_private.")]
 if any(not isinstance(row,dict) or set(row)!={"axiom","family","module","theorem"}
        or row["family"]!="h1-committed" for row in cone["native_roots"]):
  raise ValueError("native root schema mismatch")
 root_triples=[]
 for row in cone["native_roots"]:
  if (NATIVE.fullmatch(str(row.get("axiom"))) is None or theorem_modules.get(row.get("theorem"))!=row.get("module")):
   raise ValueError("native root ownership mismatch")
  root_triples.append((row["theorem"],row["module"],row["axiom"]))
 if (len(cone["theorems"])!=cone["theorem_count"] or theorem_names!=sorted(set(theorem_names))
  or not isinstance(cone["native_roots"],list) or len(cone["native_roots"])!=audit["native_root_count"]
  or root_triples!=direct_native or {row[2] for row in root_triples}!=transitive_native
  or audit["native_family_counts"]!={"h1-committed":audit["native_root_count"]}
  or audit["private_environment_theorems"]!=private_names
  or audit["private_environment_theorem_count"]!=len(private_names)
  or audit["literal_theorem_count"]!=len(theorem_names)-len(private_names)):
  raise ValueError("underlying audit theorem/root contract mismatch")
 underlying_artifacts=audit["artifacts"]
 underlying_fields={"dependency_cone","dependency_cone_sha256","discovery_log","discovery_log_sha256",
                    "print_axioms_log","print_axioms_log_sha256"}
 artifact_by_path={row["path"]:row for row in artifacts}
 if (not isinstance(underlying_artifacts,dict) or set(underlying_artifacts)!=underlying_fields
  or underlying_artifacts["dependency_cone"]!="dependency-cone.json"
  or underlying_artifacts["discovery_log"]!="dependency-cone.log"
  or underlying_artifacts["print_axioms_log"]!="print-axioms.log"
  or underlying_artifacts["dependency_cone_sha256"]!=artifact_by_path["audit/dependency-cone.json"]["sha256"]
  or underlying_artifacts["discovery_log_sha256"]!=artifact_by_path["audit/dependency-cone.log"]["sha256"]
  or underlying_artifacts["print_axioms_log_sha256"]!=artifact_by_path["audit/print-axioms.log"]["sha256"]):
  raise ValueError("underlying audit artifact crosslink mismatch")
 allowlist=read_json(child(axiom_root,"audit/allowlist.json","allowlist"),
  artifact_by_path["audit/allowlist.json"]["sha256"],"allowlist")
 if (set(allowlist)!={"allowed_axioms","native_axiom_regex","native_families","schema"}
  or allowlist.get("schema")!=1 or allowlist.get("allowed_axioms")!=sorted(FOUNDATIONAL)
  or allowlist.get("native_axiom_regex")!=NATIVE.pattern or cone.get("allowlist_sha256")!=sha(child(axiom_root,"audit/allowlist.json","allowlist"))
  or not isinstance(allowlist.get("native_families"),list) or len(allowlist["native_families"])!=1
  or set(allowlist["native_families"][0])!={"declaration_regex","id","module_regex"}
  or allowlist["native_families"][0]["id"]!="h1-committed"
  or allowlist["native_families"][0]["declaration_regex"]!="Erdos85\\..*"
  or any(re.fullmatch(allowlist["native_families"][0]["module_regex"],module) is None
         for module in set(theorem_modules.values())|{MODULE})):
  raise ValueError("allowlist crosslink mismatch")
 if axiom.get("allowlist_sha256")!=artifact_by_path["audit/allowlist.json"]["sha256"]:
  raise ValueError("top-level allowlist crosslink mismatch")
 audit_stdout=child(axiom_root,axiom["commands"]["audit"]["stdout_path"],"audit stdout")
 audit_stderr=child(axiom_root,axiom["commands"]["audit"]["stderr_path"],"audit stderr")
 if audit_stdout.read_bytes()!=child(axiom_root,audit_row["path"],"audit receipt").read_bytes() or audit_stderr.read_bytes():
  raise ValueError("audit command output crosslink mismatch")
 print_log=child(axiom_root,"audit/print-axioms.log","print axioms log")
 delimiters=[line for line in print_log.read_text().splitlines()
  if line.startswith("ERDOS85_AXIOM_BEGIN\t") or line.startswith("ERDOS85_AXIOM_END\t")]
 literal=[name for name in theorem_names if not name.startswith("_private.")]
 expected_delimiters=[item for name in literal for item in
  (f"ERDOS85_AXIOM_BEGIN\t{name}",f"ERDOS85_AXIOM_END\t{name}")]
 if delimiters!=expected_delimiters: raise ValueError("print-axioms delimiter mismatch")
 cold_path=Path(axiom["cold_receipt_path"]); cold=read_json(cold_path,axiom["cold_receipt_sha256"],"cold receipt")
 cold_fields={"cache_identity_sha256","cache_manifest_path","cache_manifest_sha256","cache_snapshot_producer_identity",
  "cache_snapshot_producer_sha256","cache_snapshot_receipt_path","cache_snapshot_receipt_sha256","commands",
  "endpoint_module","endpoint_source_path","endpoint_source_sha256","endpoint_theorem","generated_tree_identity_sha256",
  "image","materialization_evidence_path","materialization_evidence_sha256",
  "post_module_receipt_path","post_module_receipt_sha256","producer_path","producer_sha256","resource_policy",
  "retained_generated_artifacts","review_id","reviewed_control_files","schema","source_commit",
  "target_generated_artifact_path","target_olean_build_path","target_olean_bytes","target_olean_path",
  "target_olean_sha256","toolchain_path","toolchain_sha256"}
 if (set(cold)!=cold_fields or cold.get("schema")!=COLD_SCHEMA or cold.get("source_commit")!=source_commit or cold.get("image")!=IMAGE
  or cold.get("producer_path")!=str(repo/COLD_PRODUCER) or cold.get("producer_sha256")!=COLD_PRODUCER_SHA256
  or cold.get("endpoint_module")!=MODULE or cold.get("endpoint_theorem")!=THEOREM
  or cold.get("endpoint_source_path")!=SOURCE or cold.get("cache_manifest_sha256")!=axiom["cache_manifest_sha256"]
  or cold.get("toolchain_sha256")!=axiom["toolchain_sha256"]): raise ValueError("cold receipt crosslink mismatch")
 pins[str(cold_path)]=axiom["cold_receipt_sha256"]
 validate_commands(cold["commands"],cold_path.parent,pins,"cold",{"build","cache_producer_commit_oid",
  "cache_producer_worktree_oid","checkout","clone","control_commit_oids","control_worktree_oids","head",
  "lake_version","lean_version","status","status_after","tool_hashes"})
 snapshot_path=Path(axiom["cache_snapshot_receipt_path"])
 snapshot=read_json(snapshot_path,axiom["cache_snapshot_receipt_sha256"],"cache snapshot receipt")
 snapshot_fields={"cache_manifest_path","cache_manifest_sha256","control_files","entry_count","git_path","git_sha256",
  "package_count","packages","producer_path","producer_sha256","repo","schema","source_commit"}
 if (set(snapshot)!=snapshot_fields or snapshot.get("schema")!=CACHE_RECEIPT_SCHEMA or snapshot.get("source_commit")!=source_commit
  or snapshot.get("repo")!=str(repo) or snapshot.get("producer_path")!=str(repo/CACHE_PRODUCER)
  or snapshot.get("producer_sha256")!=CACHE_PRODUCER_SHA256 or snapshot.get("cache_manifest_path")!="cache-manifest.json"
  or snapshot.get("cache_manifest_sha256")!=axiom["cache_manifest_sha256"]): raise ValueError("cache snapshot crosslink mismatch")
 snapshot_identity=cold.get("cache_snapshot_producer_identity")
 if (cold.get("cache_snapshot_producer_sha256")!=CACHE_PRODUCER_SHA256 or not isinstance(snapshot_identity,dict)
  or set(snapshot_identity)!={"blob_oid","bytes","path","sha256"} or snapshot_identity.get("path")!=CACHE_PRODUCER
  or snapshot_identity.get("sha256")!=CACHE_PRODUCER_SHA256 or OID.fullmatch(str(snapshot_identity.get("blob_oid"))) is None
  or type(snapshot_identity.get("bytes")) is not int or snapshot_identity["bytes"]<=0):
  raise ValueError("cache snapshot producer identity mismatch")
 pins[str(snapshot_path)]=axiom["cache_snapshot_receipt_sha256"]
 controls=snapshot["control_files"]
 if (not isinstance(controls,list) or [row.get("path") if isinstance(row,dict) else None for row in controls]
     !=["proofs/lean-toolchain","proofs/lakefile.toml","proofs/lake-manifest.json"]
  or any(set(row)!={"blob_oid","bytes","path","sha256"} or OID.fullmatch(str(row["blob_oid"])) is None
         or SHA.fullmatch(str(row["sha256"])) is None or type(row["bytes"]) is not int or row["bytes"]<=0 for row in controls)):
  raise ValueError("control identity contract mismatch")
 packages=snapshot["packages"]; package_fields={"head","manifest_url","name","normalized_remote","path","rev","source_identity_sha256"}
 if (not isinstance(packages,list) or snapshot.get("package_count")!=len(packages)
  or any(not isinstance(row,dict) or set(row)!=package_fields or row["head"]!=row["rev"]
         or OID.fullmatch(str(row["rev"])) is None or SHA.fullmatch(str(row["source_identity_sha256"])) is None
         or re.fullmatch(r"[A-Za-z][A-Za-z0-9_-]*",str(row["name"])) is None
         or row["path"]!=str(repo/"proofs/.lake/packages"/row["name"])
         or row["normalized_remote"]!=normalize_remote(row["manifest_url"])
         for row in packages) or len({row["name"] for row in packages})!=len(packages)
  or len({row["normalized_remote"] for row in packages})!=len(packages)):
  raise ValueError("package identity contract mismatch")
 lake_manifest=json.loads((repo/"proofs/lake-manifest.json").read_bytes())
 manifest_packages=lake_manifest.get("packages") if isinstance(lake_manifest,dict) else None
 if (not isinstance(manifest_packages,list)
  or [(item.get("name"),item.get("rev"),item.get("url")) for item in manifest_packages]
     !=[(item["name"],item["rev"],item["manifest_url"]) for item in packages]):
  raise ValueError("committed Lake package provenance mismatch")
 cache_path=snapshot_path.parent/"cache-manifest.json"
 if str(cache_path)!=axiom["cache_manifest_path"] or str(cache_path)!=cold.get("cache_manifest_path"):
  raise ValueError("cache manifest path mixing")
 cache=read_json(cache_path,axiom["cache_manifest_sha256"],"cache manifest")
 if (set(cache)!={"entries","identity_sha256","root","schema"} or cache.get("schema")!=CACHE_SCHEMA
  or hashlib.sha256(canonical(cache.get("entries"))).hexdigest()!=cache.get("identity_sha256")
  or cache.get("identity_sha256")!=cold.get("cache_identity_sha256")
  or snapshot.get("entry_count")!=len(cache.get("entries",[]))): raise ValueError("cache identity mismatch")
 identity_rows(cache["entries"],"cache")
 pins[str(cache_path)]=axiom["cache_manifest_sha256"]
 cache_root=Path(cache["root"]); safe(cache_root,"cache root",kind="dir")
 if cache_root!=snapshot_path.parent/"cache": raise ValueError("cache root mixing")
 for row in cache["entries"]:
  path=child(cache_root,row["path"],"cache entry"); require(path,row["sha256"],"cache entry")
  if path.stat().st_size!=row["bytes"]: raise ValueError("cache entry bytes mismatch")
  pins[str(path)]=row["sha256"]
 observed_packages={PurePosixPath(row["path"]).parts[2] for row in cache["entries"]
  if len(PurePosixPath(row["path"]).parts)>=3 and PurePosixPath(row["path"]).parts[:2]==(".lake","packages")}
 if observed_packages!={row["name"] for row in packages}: raise ValueError("cache package set mismatch")
 for package in packages:
  subset=[row for row in cache["entries"] if PurePosixPath(row["path"]).parts[:3]==(".lake","packages",package["name"])]
  if hashlib.sha256(canonical(subset)).hexdigest()!=package["source_identity_sha256"]:
   raise ValueError("package source identity mismatch")
 toolchain_path=Path(axiom["toolchain_path"])
 toolchain=read_json(toolchain_path,axiom["toolchain_sha256"],"toolchain")
 tool_fields={"command_identity_derivation","command_templates","container_runtime_path","container_runtime_sha256",
              "git_path","git_sha256","image","resource_policy","schema"}
 cold_producer=repo/COLD_PRODUCER; spec=importlib.util.spec_from_file_location("h1_final_cold_contract",cold_producer)
 if spec is None or spec.loader is None: raise ValueError("cold producer cannot be loaded")
 cold_module=importlib.util.module_from_spec(spec); spec.loader.exec_module(cold_module)
 if (set(toolchain)!=tool_fields or toolchain.get("schema")!=TOOL_SCHEMA or toolchain.get("image")!=IMAGE
  or str(toolchain_path)!=cold["toolchain_path"] or toolchain.get("resource_policy")!=RESOURCE_POLICY
  or cold.get("resource_policy")!=RESOURCE_POLICY or toolchain.get("command_templates")!=cold_module.templates()
  or toolchain.get("command_identity_derivation")!="sha256(canonical-json({argv,cwd,environment,kind}))"
  or toolchain.get("git_path")!=snapshot["git_path"] or toolchain.get("git_sha256")!=snapshot["git_sha256"]
  or not isinstance(toolchain.get("command_templates"),dict)): raise ValueError("toolchain contract mismatch")
 if set(toolchain["command_templates"])!=set(cold["commands"]): raise ValueError("toolchain command template set mismatch")
 cold_checkout=Path(cold["commands"]["clone"]["argv"][-1]); cold_stage=Path(cold["commands"]["clone"]["cwd"])
 if (not cold_checkout.is_absolute() or cold_checkout!=cold_stage/"checkout" or cold_stage.parent!=cold_path.parent.parent
  or not cold_stage.name.startswith(".h1-cold-build-stage.")):
  raise ValueError("cold historical stage/checkout mismatch")
 substitutions={"checkout":str(cold_checkout),"commit":source_commit,"git":toolchain["git_path"],"image":IMAGE,
                "repo":str(repo),"runtime":toolchain["container_runtime_path"]}
 for kind,template in toolchain["command_templates"].items():
  if (not isinstance(template,list) or not all(isinstance(token,str) and token for token in template)):
   raise ValueError("toolchain command template malformed")
  try: expanded=[token.format_map(substitutions) for token in template]
  except (KeyError,ValueError) as error: raise ValueError("toolchain template placeholder mismatch") from error
  if cold["commands"][kind]["argv"]!=expanded or cold["commands"][kind]["cwd"]!=str(cold_stage):
   raise ValueError("cold command template expansion mismatch")
 axiom_checkout=Path(axiom["commands"]["clone"]["argv"][-1]); axiom_stage=Path(axiom["commands"]["clone"]["cwd"])
 if (not axiom_checkout.is_absolute() or axiom_checkout!=axiom_stage/"checkout"
  or axiom_stage.parent!=axiom_root.parent or not axiom_stage.name.startswith(".h1-axiom-audit-")):
  raise ValueError("axiom historical stage/checkout mismatch")
 git_text=toolchain["git_path"]; runtime_text=toolchain["container_runtime_path"]
 container=[runtime_text,"run","--rm","--pull=never","--network=none","--read-only","--cpus=8","--memory=32g",
  "--pids-limit=4096","--tmpfs","/tmp:rw,noexec,nosuid,size=2g","-v",f"{axiom_checkout}:/workspace:rw",
  "-w","/workspace",IMAGE]
 audited_paths=[item["path"] for item in axiom["audited_source_identities"]]
 project_paths=[item["path"] for item in axiom["project_cone_source_identities"]]
 expected_axiom_argv={
  "clone":[git_text,"clone","--no-hardlinks","--no-checkout",str(repo),str(axiom_checkout)],
  "checkout":[git_text,"-C",str(axiom_checkout),"checkout","--detach",source_commit],
  "head":[git_text,"-C",str(axiom_checkout),"rev-parse","HEAD"],
  "status":[git_text,"-C",str(axiom_checkout),"status","--porcelain=v1","--untracked-files=all"],
  "status_after":[git_text,"-C",str(axiom_checkout),"status","--porcelain=v1","--untracked-files=all"],
  "audit_source_commit_oids":[git_text,"-C",str(axiom_checkout),"rev-parse",*[f"{source_commit}:{p}" for p in audited_paths]],
  "audit_source_worktree_oids":[git_text,"-C",str(axiom_checkout),"hash-object","--",*audited_paths],
  "project_commit_oids":[git_text,"-C",str(axiom_checkout),"rev-parse",*[f"{source_commit}:{p}" for p in project_paths]],
  "project_worktree_oids":[git_text,"-C",str(axiom_checkout),"hash-object","--",*project_paths],
  "tool_hashes":[*container[:-1],"--entrypoint","/usr/bin/sha256sum",IMAGE,"/usr/bin/python3","/root/.elan/bin/lean","/root/.elan/bin/lake"],
  "python_version":[*container,"/usr/bin/python3","--version"],"lean_version":[*container,"lean","--version"],
  "lake_version":[*container,"lake","--version"],
  "audit":[*container,"/usr/bin/python3","scripts/erdos85_audit_dependency_cone.py","--module",MODULE,"--target",THEOREM,
           "--proofs-dir","/workspace/proofs","--allowlist","/workspace/proofs/.h1-axiom-allowlist.json",
           "--output-dir","/workspace/.h1-axiom-output"]}
 if (set(expected_axiom_argv)!=set(axiom["commands"])
  or any(axiom["commands"][kind]["argv"]!=argv or axiom["commands"][kind]["cwd"]!=str(axiom_stage)
         for kind,argv in expected_axiom_argv.items())):
  raise ValueError("axiom command template expansion mismatch")
 pins[str(toolchain_path)]=axiom["toolchain_sha256"]
 runtime=Path(toolchain["container_runtime_path"]); require(runtime,toolchain["container_runtime_sha256"],"container runtime")
 pins[str(runtime)]=toolchain["container_runtime_sha256"]
 tool_lines=child(axiom_root,axiom["commands"]["tool_hashes"]["stdout_path"],"tool hash log").read_text().splitlines()
 if (len(tool_lines)!=3 or any(re.fullmatch(r"[0-9a-f]{64}  .+",line) is None for line in tool_lines)
  or axiom.get("tool_identities")!={"python_sha256":tool_lines[0].split()[0],"lean_sha256":tool_lines[1].split()[0],
                                    "lake_sha256":tool_lines[2].split()[0]}):
  raise ValueError("tool identity mismatch")
 post_path=Path(cold["post_module_receipt_path"]); post=read_json(post_path,cold["post_module_receipt_sha256"],"post receipt")
 post_fields={"adapter_receipt_path","adapter_receipt_sha256","aggregate_layout_path","aggregate_layout_sha256",
  "bank_receipt_path","bank_receipt_sha256","capacity_reindex_receipt_path","capacity_reindex_receipt_sha256",
  "commit_object_oid","endpoint_module","endpoint_source_path","endpoint_source_sha256","endpoint_theorem",
  "evidence_path","evidence_sha256","generated_tree_identity_sha256","leaf_count","leaf_module_index_path",
  "leaf_module_index_sha256","materialization_evidence_path","materialization_evidence_sha256",
  "producer_path","producer_sha256","profile_counts","repo","review_id","reviewed_commit","schema"}
 if (set(post)!=post_fields or post.get("schema")!=POST_SCHEMA or post.get("reviewed_commit")!=source_commit
  or post.get("commit_object_oid")!=source_commit or post.get("repo")!=str(repo)
  or post.get("producer_path")!=str(repo/POST_PRODUCER) or post.get("producer_sha256")!=POST_PRODUCER_SHA256
  or post.get("endpoint_module")!=MODULE or post.get("endpoint_theorem")!=THEOREM or post.get("endpoint_source_path")!=SOURCE
  or post.get("endpoint_source_sha256")!=cold.get("endpoint_source_sha256") or post.get("leaf_count")!=13351
  or post.get("profile_counts")!=PROFILE_COUNTS or post.get("review_id")!=cold.get("review_id")
  or post.get("generated_tree_identity_sha256")!=cold.get("generated_tree_identity_sha256")
  or post.get("materialization_evidence_path")!=cold.get("materialization_evidence_path")
  or post.get("materialization_evidence_sha256")!=cold.get("materialization_evidence_sha256")
  or cold.get("reviewed_control_files")!=controls):
  raise ValueError("post-module receipt crosslink mismatch")
 if sum(post["profile_counts"])!=post["leaf_count"]: raise ValueError("post-module profile sum mismatch")
 pins[str(post_path)]=cold["post_module_receipt_sha256"]
 for path_key,pin_key in (("adapter_receipt_path","adapter_receipt_sha256"),("aggregate_layout_path","aggregate_layout_sha256"),
  ("bank_receipt_path","bank_receipt_sha256"),("capacity_reindex_receipt_path","capacity_reindex_receipt_sha256"),
  ("leaf_module_index_path","leaf_module_index_sha256"),
  ("materialization_evidence_path","materialization_evidence_sha256"),("producer_path","producer_sha256")):
  path=Path(post[path_key]); require(path,post[pin_key],f"post {path_key}"); pins[str(path)]=post[pin_key]
 evidence_path=child(post_path.parent,post["evidence_path"],"post evidence")
 evidence=read_json(evidence_path,post["evidence_sha256"],"post evidence")
 evidence_fields={"adapter_repo_path","adapter_source_identity","aggregate_layout_source_identity",
  "aggregate_tree_identity_sha256","generated_tree_identity_sha256","leaf_count","leaf_tree_identity_sha256",
  "profile_counts","review_id","reviewed_commit","rows","schema"}
 if (set(evidence)!=evidence_fields or evidence.get("schema")!=EVIDENCE_SCHEMA or evidence.get("reviewed_commit")!=source_commit
  or evidence.get("leaf_count")!=13351 or evidence.get("profile_counts")!=PROFILE_COUNTS
  or evidence.get("review_id")!=post["review_id"] or evidence.get("adapter_repo_path")!=SOURCE
  or evidence.get("generated_tree_identity_sha256")!=post["generated_tree_identity_sha256"]
  or not isinstance(evidence.get("rows"),list) or len(evidence["rows"])!=13351):
  raise ValueError("terminal capacity evidence mismatch")
 pins[str(evidence_path)]=post["evidence_sha256"]
 evidence_row_fields={"capacity_local_index","compact_lrat_sha256","leaf_blob_oid","leaf_repo_path","leaf_source_bytes","leaf_source_sha256",
  "ledger_path","ledger_sha256","packed_path","packed_sha256","profile","replay_evidence_path","replay_evidence_sha256","tag"}
 evidence_row_fields.update({"materialized_olean_sha256","replay_ready_key","replay_ready_sha256",
                             "replay_receipt_key","replay_receipt_sha256"})
 observed_profiles=[[] for _ in PROFILE_COUNTS]; tags=set()
 for row in evidence["rows"]:
  if (not isinstance(row,dict) or set(row)!=evidence_row_fields or type(row["profile"]) is not int
   or row["profile"] not in range(5) or type(row["capacity_local_index"]) is not int
   or OID.fullmatch(str(row["leaf_blob_oid"])) is None or type(row["leaf_source_bytes"]) is not int
   or row["leaf_source_bytes"]<=0 or any(SHA.fullmatch(str(row[key])) is None for key in
      ("leaf_source_sha256","ledger_sha256","packed_sha256","replay_evidence_sha256"))
   or re.fullmatch(r"[0-9a-f]{16}",str(row["tag"])) is None or row["tag"] in tags):
   raise ValueError("terminal capacity evidence row malformed")
  for key in ("leaf_repo_path","ledger_path","packed_path","replay_evidence_path"): rel(row[key],f"evidence {key}")
  tags.add(row["tag"]); observed_profiles[row["profile"]].append(row["capacity_local_index"])
 if any(values!=list(range(count)) for values,count in zip(observed_profiles,PROFILE_COUNTS,strict=True)):
  raise ValueError("terminal capacity evidence index coverage mismatch")
 bank_root=Path(post["bank_receipt_path"]).parent; safe(bank_root,"payload bank root",kind="dir")
 terminal_files={}
 for row in evidence["rows"]:
  for path_key,pin_key in (("ledger_path","ledger_sha256"),("packed_path","packed_sha256"),
                           ("replay_evidence_path","replay_evidence_sha256")):
   path=child(bank_root,row[path_key],f"terminal {path_key}")
   prior=terminal_files.get(str(path))
   if prior is not None and prior!=row[pin_key]: raise ValueError("terminal evidence identity mixing")
   terminal_files[str(path)]=row[pin_key]
 for text,pin in terminal_files.items(): require(Path(text),pin,"terminal evidence file"); pins[text]=pin
 bank_path=Path(post["bank_receipt_path"]); bank=read_json(bank_path,post["bank_receipt_sha256"],"payload bank receipt")
 bank_fields={"all_even_manifest_path","all_even_manifest_sha256","capacity_inventory_path","capacity_inventory_sha256",
  "compact_universe_path","compact_universe_sha256","complement_manifest_path","complement_manifest_sha256",
  "coverage_receipt_path","coverage_receipt_sha256","coverage_terminal_counts","leaf_count","ledger_snapshot_path",
  "ledger_snapshot_sha256","materializer_sha256","materializer_source","payload_identity_sha256","payload_index_path",
  "payload_index_sha256","profile_counts","replay_audit_path","replay_audit_sha256","s3_bucket","s3_prefix","schema",
  "selected_ledger_identity_sha256","source_index_path","source_index_sha256","toolchain_path","toolchain_sha256"}
 if (set(bank)!=bank_fields or bank.get("schema")!=BANK_SCHEMA or bank.get("leaf_count")!=13351
  or bank.get("profile_counts")!=PROFILE_COUNTS or sum(bank["profile_counts"])!=bank["leaf_count"]
  or bank.get("coverage_terminal_counts")!=TERMINAL_COUNTS
  or bank.get("materializer_source")!=BANK_PRODUCER or bank.get("materializer_sha256")!=BANK_PRODUCER_SHA256):
  raise ValueError("payload bank receipt contract mismatch")
 capacity_inventory=Path(bank["capacity_inventory_path"]); require(capacity_inventory,bank["capacity_inventory_sha256"],"capacity inventory")
 pins[str(capacity_inventory)]=bank["capacity_inventory_sha256"]
 ledger_receipt_path=Path(bank["ledger_snapshot_path"])
 ledger_receipt=read_json(ledger_receipt_path,bank["ledger_snapshot_sha256"],"selected ledger receipt")
 ledger_receipt_fields={"capacity_inventory_path","capacity_inventory_sha256","coverage_receipt_path",
  "coverage_receipt_sha256","inventory_helper_path","inventory_helper_sha256","leaf_count","ledger_roots",
  "producer_path","producer_sha256","profile_counts","schema","selected_ledger_identity_sha256","snapshot_path","snapshot_sha256"}
 if (set(ledger_receipt)!=ledger_receipt_fields or ledger_receipt.get("schema")!=LEDGER_RECEIPT_SCHEMA
  or ledger_receipt.get("capacity_inventory_path")!=str(capacity_inventory)
  or ledger_receipt.get("capacity_inventory_sha256")!=bank["capacity_inventory_sha256"]
  or ledger_receipt.get("coverage_receipt_path")!=bank["coverage_receipt_path"]
  or ledger_receipt.get("coverage_receipt_sha256")!=bank["coverage_receipt_sha256"]
  or ledger_receipt.get("leaf_count")!=13351 or ledger_receipt.get("profile_counts")!=PROFILE_COUNTS
  or ledger_receipt.get("selected_ledger_identity_sha256")!=bank["selected_ledger_identity_sha256"]
  or set(ledger_receipt.get("ledger_roots",{}))!={"host","v2","v3"}
  or ledger_receipt.get("producer_path")!=str(repo/LEDGER_PRODUCER)
  or ledger_receipt.get("producer_sha256")!=LEDGER_PRODUCER_SHA256):
  raise ValueError("selected ledger receipt mismatch")
 pins[str(ledger_receipt_path)]=bank["ledger_snapshot_sha256"]
 if any(not isinstance(item,dict) or set(item)!={"count","identity_sha256","path"}
        or type(item["count"]) is not int or item["count"]<0
        or SHA.fullmatch(str(item["identity_sha256"])) is None for item in ledger_receipt["ledger_roots"].values()):
  raise ValueError("ledger root identity malformed")
 inventory_helper=Path(ledger_receipt["inventory_helper_path"])
 require(inventory_helper,ledger_receipt["inventory_helper_sha256"],"ledger inventory helper")
 pins[str(inventory_helper)]=ledger_receipt["inventory_helper_sha256"]
 coverage_path=Path(bank["coverage_receipt_path"])
 coverage=read_json(coverage_path,bank["coverage_receipt_sha256"],"coverage receipt")
 coverage_fields={"aws","host_ledger_snapshot","inputs","live_campaign","live_named_output_paths",
  "live_named_outputs_mutated","live_outputs_after","live_outputs_before","outputs","schema","summary","timestamp_utc"}
 summary_fields={"anomalies","certified","cnf_sha_comparable_count","cnf_sha_divergent_count","fleet_claim_tags",
  "fleet_in_flight","fleet_ledger_rows","fleet_unknown_without_cert","host_ledger_rows","pending","status_total",
  "unknown_tags"}
 coverage_input_fields={"all_even_manifest","all_even_manifest_sha256","compact_inventory","compact_inventory_sha256",
  "complement_manifest","complement_manifest_sha256","publisher","publisher_sha256","reconciler","reconciler_sha256"}
 summary=coverage.get("summary"); coverage_inputs=coverage.get("inputs")
 unknown_keys={"certified_s3","fleet_v2_claim","fleet_v2_ledger","fleet_v3_claim","fleet_v3_ledger","host_ledger"}
 if (set(coverage)!=coverage_fields or coverage.get("schema")!=COVERAGE_SCHEMA
  or not isinstance(summary,dict) or set(summary)!=summary_fields or not isinstance(coverage_inputs,dict)
  or set(coverage_inputs)!=coverage_input_fields or coverage.get("live_named_outputs_mutated") is not False
  or coverage.get("live_outputs_before")!=coverage.get("live_outputs_after")
  or not isinstance(coverage.get("aws"),dict) or set(coverage["aws"])!={"bucket","profile","s3_prefix"}
  or any(not isinstance(coverage["aws"][key],str) or not coverage["aws"][key] for key in coverage["aws"])
  or coverage["aws"]["bucket"]!=bank["s3_bucket"] or coverage["aws"]["s3_prefix"]!=bank["s3_prefix"]
  or re.fullmatch(r"\d{4}-\d\d-\d\dT\d\d:\d\d:\d\dZ",str(coverage.get("timestamp_utc"))) is None
  or not isinstance(coverage.get("host_ledger_snapshot"),dict)
  or set(coverage["host_ledger_snapshot"])!={"count","identity_sha256"}
  or type(coverage["host_ledger_snapshot"]["count"]) is not int or coverage["host_ledger_snapshot"]["count"]<0
  or SHA.fullmatch(str(coverage["host_ledger_snapshot"]["identity_sha256"])) is None
  or {key:summary.get(key) for key in TERMINAL_COUNTS}!=TERMINAL_COUNTS or summary.get("anomalies")!={}
  or summary.get("cnf_sha_divergent_count")!=0 or summary.get("fleet_unknown_without_cert")!=0
  or not isinstance(summary.get("unknown_tags"),dict) or set(summary["unknown_tags"])!=unknown_keys
  or any(value!=[] for value in summary["unknown_tags"].values())):
  raise ValueError("coverage is not terminal")
 live_paths=coverage.get("live_named_output_paths"); live_before=coverage.get("live_outputs_before")
 if (not isinstance(live_paths,dict) or set(live_paths)!={"counts.json","coverage.tsv","inventory_universe_diff.tsv"}
  or not isinstance(live_before,dict) or set(live_before)!=set(live_paths)
  or any(not isinstance(item,dict) or set(item)!={"bytes","sha256"} or type(item["bytes"]) is not int
         or item["bytes"]<0 or SHA.fullmatch(str(item["sha256"])) is None for item in live_before.values())
  or any(not isinstance(value,str) or not Path(value).is_absolute() for value in live_paths.values())):
  raise ValueError("coverage live provenance mismatch")
 coverage_root=coverage_path.parent; coverage_outputs=coverage.get("outputs")
 if not isinstance(coverage_outputs,dict) or set(coverage_outputs)!={"counts.json","coverage.tsv","inventory_universe_diff.tsv"}:
  raise ValueError("coverage output set mismatch")
 for name,item in coverage_outputs.items():
  if (not isinstance(item,dict) or set(item)!={"bytes","sha256"} or type(item["bytes"]) is not int
   or item["bytes"]<0): raise ValueError("coverage output identity malformed")
  path=coverage_root/name; require(path,item["sha256"],f"coverage {name}")
  if path.stat().st_size!=item["bytes"]: raise ValueError("coverage output byte mismatch")
  pins[str(path)]=item["sha256"]
 for path_key,pin_key in (("all_even_manifest","all_even_manifest_sha256"),("compact_inventory","compact_inventory_sha256"),
  ("complement_manifest","complement_manifest_sha256"),("publisher","publisher_sha256"),("reconciler","reconciler_sha256")):
  path=Path(coverage_inputs[path_key]); require(path,coverage_inputs[pin_key],f"coverage {path_key}"); pins[str(path)]=coverage_inputs[pin_key]
 if (coverage_inputs["all_even_manifest"]!=bank["all_even_manifest_path"]
  or coverage_inputs["all_even_manifest_sha256"]!=bank["all_even_manifest_sha256"]
  or coverage_inputs["compact_inventory"]!=bank["compact_universe_path"]
  or coverage_inputs["compact_inventory_sha256"]!=bank["compact_universe_sha256"]
  or coverage_inputs["complement_manifest"]!=bank["complement_manifest_path"]
  or coverage_inputs["complement_manifest_sha256"]!=bank["complement_manifest_sha256"]):
  raise ValueError("coverage/bank input mixing")
 counts_raw=(coverage_root/"counts.json").read_bytes(); counts=json.loads(counts_raw)
 count_fields={"all_even_capacity","anomalies","capacity_inventory_total","capacity_only_error","certified_s3_tags",
  "cnf_sha_comparable_count","cnf_sha_divergent_count","cnf_sha_divergent_tags","compact_inventory_total",
  "compact_only_pre_capacity","fleet_claim_tags","fleet_ledger_rows","fleet_unknown_without_cert","fleet_v2_claim_tags",
  "fleet_v2_ledger_rows","fleet_v3_claim_tags","fleet_v3_ledger_rows","host_ledger_rows","non_all_even_capacity",
  "status_counts","status_total","unknown_tags"}
 if (not isinstance(counts,dict) or set(counts)!=count_fields or counts.get("capacity_inventory_total")!=13351
  or counts.get("certified_s3_tags")!=13351 or counts.get("status_total")!=13351
  or counts.get("status_counts")!={"certified-in-S3":13351,"fleet-in-flight":0,"pending":0}
  or counts.get("anomalies")!={} or counts.get("capacity_only_error")!=0
  or counts.get("compact_inventory_total")!=13541 or counts.get("compact_only_pre_capacity")!=190
  or counts.get("cnf_sha_divergent_count")!=0 or counts.get("cnf_sha_divergent_tags")!=[]
  or counts.get("fleet_unknown_without_cert")!=0 or not isinstance(counts.get("unknown_tags"),dict)
  or set(counts["unknown_tags"])!=unknown_keys
  or any(value!=[] for value in counts["unknown_tags"].values()) or counts_raw!=canonical(counts)):
  raise ValueError("coverage counts are not terminal")
 if (coverage_root/"inventory_universe_diff.tsv").read_bytes()!=b"tag\trelation\tcompact_profile\tcapacity_source\n":
  raise ValueError("coverage universe diff is not empty")
 coverage_header=("tag","profile","family","local_index","inventory_source","status","certified_s3","host_unsat",
  "host_cnf_sha256","host_verdict","fleet_claim","fleet_cnf_sha256","fleet_verdict","cnf_sha_divergent",
  "fleet_v2_claim","fleet_v2_cnf_sha256","fleet_v2_verdict","fleet_v3_claim","fleet_v3_cnf_sha256","fleet_v3_verdict")
 with (coverage_root/"coverage.tsv").open(newline="") as stream:
  reader=csv.DictReader(stream,delimiter="\t")
  if tuple(reader.fieldnames or ())!=coverage_header: raise ValueError("coverage header mismatch")
  coverage_rows=list(reader)
 if (len(coverage_rows)!=13351 or [row.get("tag") for row in coverage_rows]!=[row["tag"] for row in evidence["rows"]]
  or any(row.get("status")!="certified-in-S3" or row.get("certified_s3")!="1"
         or row.get("cnf_sha_divergent")!="0" for row in coverage_rows)):
  raise ValueError("coverage row terminality mismatch")
 pins[str(coverage_path)]=bank["coverage_receipt_sha256"]
 payload_path=Path(bank["payload_index_path"]); replay_audit_path=Path(bank["replay_audit_path"])
 if payload_path!=bank_root/"payload-index.json" or replay_audit_path!=bank_root/"replay-audit.json":
  raise ValueError("payload bank nested path mismatch")
 payload=read_json(payload_path,bank["payload_index_sha256"],"payload index")
 replay_audit=read_json(replay_audit_path,bank["replay_audit_sha256"],"replay audit")
 if (set(payload)!={"capacity_inventory_sha256","profile_counts","rows","schema"}
  or set(replay_audit)!={"capacity_inventory_sha256","coverage_receipt_sha256","profile_counts","rows",
                         "replay_evidence_identity_sha256","schema"}
  or payload.get("schema")!=PAYLOAD_SCHEMA or replay_audit.get("schema")!=REPLAY_AUDIT_SCHEMA
  or payload.get("capacity_inventory_sha256")!=bank["capacity_inventory_sha256"]
  or replay_audit.get("capacity_inventory_sha256")!=bank["capacity_inventory_sha256"]
  or replay_audit.get("coverage_receipt_sha256")!=bank["coverage_receipt_sha256"]
  or payload.get("profile_counts")!=PROFILE_COUNTS or replay_audit.get("profile_counts")!=PROFILE_COUNTS
  or len(payload.get("rows",[]))!=13351 or len(replay_audit.get("rows",[]))!=13351
  or hashlib.sha256(canonical(replay_audit.get("rows"))).hexdigest()!=replay_audit.get("replay_evidence_identity_sha256")):
  raise ValueError("payload/replay audit crosslink mismatch")
 payload_fields={"binary_bytes","binary_lrat_sha256","capacity_local_index","cnf_sha256","compact_bytes",
  "compact_lrat_sha256","gzip_bytes","gzip_sha256","ledger_namespace","ledger_path","ledger_sha256","lrat_actions",
  "lz4_frame_bytes","lz4_frame_sha256","packed_lz4_bytes","packed_lz4_path","packed_lz4_sha256","profile",
  "raw_lrat_bytes","raw_lrat_sha256","s3_key","source_cnf_clauses","tag"}
 replay_audit_fields={"ledger_namespace","ledger_sha256","packed_lz4_sha256","replay_evidence_path",
  "replay_evidence_sha256","replay_command_identity_sha256","s3_key","tag"}
 if (any(not isinstance(row,dict) or set(row)!=payload_fields for row in payload["rows"])
  or any(not isinstance(row,dict) or set(row)!=replay_audit_fields for row in replay_audit["rows"])):
  raise ValueError("payload/replay row schema mismatch")
 for evidence_row,payload_row,audit_row in zip(evidence["rows"],payload["rows"],replay_audit["rows"],strict=True):
  coordinate=(evidence_row["tag"],evidence_row["profile"],evidence_row["capacity_local_index"])
  if (any(type(payload_row[key]) is not int or payload_row[key]<0 for key in
          ("binary_bytes","compact_bytes","gzip_bytes","lrat_actions","lz4_frame_bytes","packed_lz4_bytes",
           "raw_lrat_bytes","source_cnf_clauses"))
   or any(SHA.fullmatch(str(payload_row[key])) is None for key in payload_row if key.endswith("sha256"))
   or any(SHA.fullmatch(str(audit_row[key])) is None for key in audit_row if key.endswith("sha256"))
   or (payload_row["tag"],payload_row["profile"],payload_row["capacity_local_index"])!=coordinate
   or audit_row["tag"]!=evidence_row["tag"] or payload_row["ledger_path"]!=evidence_row["ledger_path"]
   or audit_row["ledger_namespace"]!=payload_row["ledger_namespace"]
   or audit_row["ledger_sha256"]!=payload_row["ledger_sha256"] or audit_row["s3_key"]!=payload_row["s3_key"]
   or audit_row["packed_lz4_sha256"]!=payload_row["packed_lz4_sha256"]
   or payload_row["ledger_sha256"]!=evidence_row["ledger_sha256"]
   or payload_row["packed_lz4_path"]!=evidence_row["packed_path"]
   or payload_row["packed_lz4_sha256"]!=evidence_row["packed_sha256"]
   or audit_row["replay_evidence_path"]!=evidence_row["replay_evidence_path"]
   or audit_row["replay_evidence_sha256"]!=evidence_row["replay_evidence_sha256"]):
   raise ValueError("payload/replay/evidence identity mixing")
  packed_path=child(bank_root,payload_row["packed_lz4_path"],"packed payload")
  if packed_path.stat().st_size!=payload_row["packed_lz4_bytes"]: raise ValueError("packed payload byte mismatch")
  replay_path=child(bank_root,audit_row["replay_evidence_path"],"replay evidence")
  replay_value=read_json(replay_path,audit_row["replay_evidence_sha256"],"replay evidence")
  replay_fields={"accepted_marker","commands","cnf_sha256","compact_bytes","compact_lrat_sha256","image",
                 "lratreplay_sha256","schema","table_path","table_sha256","tag"}
  expected_command_kinds={"cnf_check","cnf_emit","compress","decode","encode","fetch","replay","replay_pin","v2cnf_pin"}
  replay_command_fields={"argv","command_identity_sha256","cumulative_children_maxrss_kb","cwd","environment","kind",
   "rc","stderr_bytes","stderr_path","stderr_sha256","stdout_bytes","stdout_path","stdout_sha256","system_ns",
   "user_ns","wall_ns"}
  commands=replay_value.get("commands")
  if (set(replay_value)!=replay_fields or replay_value.get("schema")!=REPLAY_SCHEMA
   or replay_value.get("accepted_marker")!="LRAT accepted: true" or replay_value.get("image")!=IMAGE
   or replay_value.get("tag")!=evidence_row["tag"] or replay_value.get("cnf_sha256")!=payload_row["cnf_sha256"]
   or replay_value.get("compact_lrat_sha256")!=payload_row["compact_lrat_sha256"]
   or replay_value.get("compact_bytes")!=payload_row["compact_bytes"]
   or not isinstance(commands,dict) or set(commands)!=expected_command_kinds
   or any(not isinstance(record,dict) or set(record)!=replay_command_fields or record.get("kind")!=kind
          or not isinstance(record.get("argv"),list) or not all(isinstance(token,str) and token for token in record["argv"])
          or record.get("environment")!={} or record.get("rc")!=0
          or any(type(record.get(key)) is not int or record[key]<0 for key in
                 ("cumulative_children_maxrss_kb","rc","system_ns","user_ns","wall_ns","stdout_bytes","stderr_bytes"))
          or record["wall_ns"]<=0 or record["cumulative_children_maxrss_kb"]<=0 for kind,record in commands.items())
   or commands["replay"]["command_identity_sha256"]!=audit_row["replay_command_identity_sha256"]):
   raise ValueError("replay evidence contract mismatch")
  for kind,record in commands.items():
   core={"argv":record["argv"],"cwd":record["cwd"],"environment":{},"kind":kind}
   if record["command_identity_sha256"]!=hashlib.sha256(canonical(core)).hexdigest():
    raise ValueError("replay command identity mismatch")
   for stream in ("stdout","stderr"):
    retained=record[f"{stream}_path"]
    if retained is None:
     if (kind,stream) not in {("cnf_emit","stdout"),("decode","stdout")}: raise ValueError("replay log missing")
    else:
     log=child(bank_root,retained,"replay command log"); require(log,record[f"{stream}_sha256"],"replay command log")
     if log.stat().st_size!=record[f"{stream}_bytes"]: raise ValueError("replay command log bytes mismatch")
     pins[str(log)]=record[f"{stream}_sha256"]
  table_path=child(bank_root,replay_value["table_path"],"replay table")
  require(table_path,replay_value["table_sha256"],"replay table"); pins[str(table_path)]=replay_value["table_sha256"]
 ledger_snapshot_path=ledger_receipt_path.parent/ledger_receipt["snapshot_path"]
 ledger_snapshot=read_json(ledger_snapshot_path,ledger_receipt["snapshot_sha256"],"selected ledger snapshot")
 if (set(ledger_snapshot)!={"capacity_inventory_sha256","coverage_receipt_sha256","profile_counts","rows","schema"}
  or ledger_snapshot.get("schema")!=LEDGER_SCHEMA
  or ledger_snapshot.get("capacity_inventory_sha256")!=bank["capacity_inventory_sha256"]
  or ledger_snapshot.get("coverage_receipt_sha256")!=bank["coverage_receipt_sha256"]
  or ledger_snapshot.get("profile_counts")!=PROFILE_COUNTS or len(ledger_snapshot.get("rows",[]))!=13351):
  raise ValueError("selected ledger snapshot mismatch")
 for payload_row,snapshot_row in zip(payload["rows"],ledger_snapshot["rows"],strict=True):
  certificate_fields={"p","i","cnf_sha256","cnf_clauses","raw_lrat_sha256","raw_lrat_bytes",
                      "compact_lrat_sha256","compact_bytes","compact_gz_sha256"}
  if (not isinstance(snapshot_row,dict) or set(snapshot_row)!={"capacity_local_index","certificate_identity","selected","sources","tag"}
   or snapshot_row["tag"]!=payload_row["tag"] or snapshot_row["capacity_local_index"]!=payload_row["capacity_local_index"]
   or not isinstance(snapshot_row["selected"],dict) or set(snapshot_row["selected"])!={"namespace","path","sha256"}
   or snapshot_row["selected"]!={"namespace":payload_row["ledger_namespace"],"path":payload_row["ledger_path"],
                                 "sha256":payload_row["ledger_sha256"]}
   or not isinstance(snapshot_row["certificate_identity"],dict) or set(snapshot_row["certificate_identity"])!=certificate_fields
   or snapshot_row["certificate_identity"]["cnf_sha256"]!=payload_row["cnf_sha256"]
   or snapshot_row["certificate_identity"]["raw_lrat_sha256"]!=payload_row["raw_lrat_sha256"]
   or snapshot_row["certificate_identity"]["compact_lrat_sha256"]!=payload_row["compact_lrat_sha256"]
   or snapshot_row["certificate_identity"]["compact_gz_sha256"]!=payload_row["gzip_sha256"]
   or not isinstance(snapshot_row["sources"],dict) or set(snapshot_row["sources"])!={"host","v2","v3"}
   or not isinstance(snapshot_row["sources"].get(payload_row["ledger_namespace"]),dict)
   or snapshot_row["sources"][payload_row["ledger_namespace"]].get("sha256")!=payload_row["ledger_sha256"]):
   raise ValueError("selected ledger row mismatch")
 pins[str(ledger_snapshot_path)]=ledger_receipt["snapshot_sha256"]
 expected_payload_identity=hashlib.sha256(canonical([{"bytes":row["packed_lz4_bytes"],
  "path":row["packed_lz4_path"],"sha256":row["packed_lz4_sha256"]} for row in payload["rows"]])).hexdigest()
 if expected_payload_identity!=bank["payload_identity_sha256"]: raise ValueError("payload identity mismatch")
 ledger_identities=[{"bytes":child(bank_root,row["ledger_path"],"selected ledger").stat().st_size,
  "path":row["ledger_path"],"sha256":row["ledger_sha256"]} for row in payload["rows"]]
 if hashlib.sha256(canonical(ledger_identities)).hexdigest()!=bank["selected_ledger_identity_sha256"]:
  raise ValueError("selected ledger identity mismatch")
 source_index_path=Path(bank["source_index_path"]); require(source_index_path,bank["source_index_sha256"],"bank source index")
 source_columns=("orbit","profile","localIndex","compact_lrat_sha256","raw_lrat_sha256","cnf_sha256","lrat_actions",
  "source_cnf_clauses","compact_bytes","stub_ready","binary_lrat_sha256","binary_bytes","lz4_frame_sha256",
  "lz4_frame_bytes","packed_lz4_sha256","packed_lz4_bytes")
 with source_index_path.open(newline="") as stream:
  reader=csv.DictReader(stream,delimiter="\t")
  if tuple(reader.fieldnames or ())!=source_columns: raise ValueError("bank source index header mismatch")
  source_rows=list(reader)
 expected_source_rows=[{"orbit":row["tag"],"profile":PROFILE_NAMES[row["profile"]],
  "localIndex":str(row["capacity_local_index"]),"compact_lrat_sha256":row["compact_lrat_sha256"],
  "raw_lrat_sha256":row["raw_lrat_sha256"],"cnf_sha256":row["cnf_sha256"],
  "lrat_actions":str(row["lrat_actions"]),"source_cnf_clauses":str(row["source_cnf_clauses"]),
  "compact_bytes":str(row["compact_bytes"]),"stub_ready":"1",
  "binary_lrat_sha256":row["binary_lrat_sha256"],"binary_bytes":str(row["binary_bytes"]),
  "lz4_frame_sha256":row["lz4_frame_sha256"],"lz4_frame_bytes":str(row["lz4_frame_bytes"]),
  "packed_lz4_sha256":row["packed_lz4_sha256"],"packed_lz4_bytes":str(row["packed_lz4_bytes"])}
  for row in payload["rows"]]
 if len(source_rows)!=13351 or source_rows!=expected_source_rows:
  raise ValueError("bank source index ordering mismatch")
 pins[str(source_index_path)]=bank["source_index_sha256"]
 bank_tool_path=Path(bank["toolchain_path"]); bank_tool=read_json(bank_tool_path,bank["toolchain_sha256"],"bank toolchain")
 bank_tool_fields={"aws_path","aws_sha256","command_identity_derivation","command_templates","compressor_sha256",
  "container_runtime_path","container_runtime_sha256","encoder_sha256","environments","image","lratreplay_sha256",
  "lz4_args","lz4_path","lz4_sha256","lz4_version","python_path","python_sha256","v2cnf_sha256",
  "producer_helpers","schema"}
 if (set(bank_tool)!=bank_tool_fields or bank_tool.get("schema")!=BANK_TOOL_SCHEMA or bank_tool.get("image")!=IMAGE
  or bank_tool.get("lratreplay_sha256")!="37aad1d5c64a75fcb68e1ea587b2080b06c157a19c883b01d145b28b891c428c"
  or bank_tool.get("lz4_args")!=["-q","-f","-12","-T1","-BI","-B7","--content-size","--no-frame-crc"]
  or any(SHA.fullmatch(str(bank_tool.get(key))) is None for key in
         ("aws_sha256","compressor_sha256","container_runtime_sha256","encoder_sha256","lratreplay_sha256",
          "lz4_sha256","python_sha256","v2cnf_sha256"))): raise ValueError("bank toolchain contract mismatch")
 bank_producer=repo/BANK_PRODUCER
 bank_spec=importlib.util.spec_from_file_location("h1_final_bank_contract",bank_producer)
 if bank_spec is None or bank_spec.loader is None: raise ValueError("bank producer import failed")
 bank_module=importlib.util.module_from_spec(bank_spec); sys.modules[bank_spec.name]=bank_module
 bank_spec.loader.exec_module(bank_module)
 helpers=[{"source":name,"sha256":sha(repo/"research/problems/erdos-85-wip-01/sat49"/name)} for name in
  ("filter_h1_capacity_inventory.py","encode_h1_v2_binary_lrat.py","compress_h1_v2_binary_lrat.py")]
 if (bank_tool.get("producer_helpers")!=helpers or bank_tool.get("encoder_sha256")!=helpers[1]["sha256"]
  or bank_tool.get("compressor_sha256")!=helpers[2]["sha256"]):
  raise ValueError("bank toolchain helper identity mismatch")
 fetch_environment=bank_tool.get("environments",{}).get("fetch",{})
 fetch_home=Path(fetch_environment["HOME"]) if fetch_environment.get("HOME") else None
 fetch_config=Path(fetch_environment["AWS_CONFIG_FILE"]) if fetch_environment.get("AWS_CONFIG_FILE") else None
 fetch_credentials=Path(fetch_environment["AWS_SHARED_CREDENTIALS_FILE"]) \
  if fetch_environment.get("AWS_SHARED_CREDENTIALS_FILE") else None
 if (bank_tool.get("command_templates")!=bank_module.expected_templates()
  or bank_tool.get("command_identity_derivation")!="sha256(canonical-json({argv,cwd,environment,kind}))"
  or set(bank_tool.get("environments",{}))!=set(bank_module.expected_templates())
  or any(not isinstance(env,dict) or any(not isinstance(key,str) or not isinstance(value,str)
   for key,value in env.items()) for env in bank_tool.get("environments",{}).values())
  or fetch_environment.get("AWS_PROFILE")!=coverage["aws"]["profile"]
  or set(fetch_environment)-{"AWS_PROFILE","AWS_CONFIG_FILE","AWS_SHARED_CREDENTIALS_FILE",
                              "AWS_EC2_METADATA_DISABLED","HOME"}
  or not (fetch_environment.get("HOME") or
          (fetch_environment.get("AWS_CONFIG_FILE") and fetch_environment.get("AWS_SHARED_CREDENTIALS_FILE")))
  or (fetch_home is not None and (not fetch_home.is_absolute() or fetch_home!=fetch_home.resolve()
      or fetch_home.is_symlink() or not fetch_home.is_dir()))
  or (fetch_home is None and any(path is None or not path.is_absolute() or path!=path.resolve()
      or path.is_symlink() or not path.is_file() for path in (fetch_config,fetch_credentials)))
  or any(bank_tool["environments"][kind]!={} for kind in set(bank_module.expected_templates())-{"fetch"})
  or not isinstance(bank_tool.get("lz4_version"),str) or not bank_tool["lz4_version"]):
  raise ValueError("bank toolchain command contract mismatch")
 for helper in helpers: pins[str(repo/"research/problems/erdos-85-wip-01/sat49"/helper["source"])]=helper["sha256"]
 for path_key,pin_key in (("aws_path","aws_sha256"),("container_runtime_path","container_runtime_sha256"),
  ("lz4_path","lz4_sha256"),("python_path","python_sha256")):
  path=Path(bank_tool[path_key]); require(path,bank_tool[pin_key],f"bank tool {path_key}"); pins[str(path)]=bank_tool[pin_key]
 pins[str(bank_tool_path)]=bank["toolchain_sha256"]
 pins[str(payload_path)]=bank["payload_index_sha256"]; pins[str(replay_audit_path)]=bank["replay_audit_sha256"]

 def nested_receipt(path_key,pin_key,label,pretty=False):
  path=Path(post[path_key]); require(path,post[pin_key],label); raw=path.read_bytes(); value=json.loads(raw)
  expected=(json.dumps(value,indent=2,sort_keys=True)+"\n").encode() if pretty else canonical(value)
  if not isinstance(value,dict) or raw!=expected: raise ValueError(f"{label} serialization mismatch")
  return path,value
 reindex_path,reindex=nested_receipt("capacity_reindex_receipt_path","capacity_reindex_receipt_sha256","reindex receipt",True)
 reindex_fields={"capacity_total","dropped_outside_capacity_tags","emitted_rows","indexes","inventory",
  "inventory_sha256","output","output_sha256","require_complete","schema"}
 if (set(reindex)!=reindex_fields or reindex.get("schema")!=REINDEX_SCHEMA or reindex.get("capacity_total")!=13351
  or reindex.get("emitted_rows")!=13351 or reindex.get("dropped_outside_capacity_tags")!=[]
  or reindex.get("require_complete") is not True or reindex.get("inventory")!=bank["capacity_inventory_path"]
  or reindex.get("inventory_sha256")!=bank["capacity_inventory_sha256"]): raise ValueError("reindex/bank mismatch")
 if not isinstance(reindex["indexes"],list) or not reindex["indexes"]: raise ValueError("reindex source indexes missing")
 reindex_index_paths=set()
 for item in reindex["indexes"]:
  if not isinstance(item,dict) or set(item)!={"path","sha256"}: raise ValueError("reindex source index malformed")
  path=Path(item["path"]); require(path,item["sha256"],"reindex source index")
  if str(path) in reindex_index_paths: raise ValueError("reindex source index duplicate")
  reindex_index_paths.add(str(path)); pins[str(path)]=item["sha256"]
 reindex_output=Path(reindex["output"]); require(reindex_output,reindex["output_sha256"],"reindex output")
 pins[str(reindex_output)]=reindex["output_sha256"]
 layout_path,layout=nested_receipt("aggregate_layout_path","aggregate_layout_sha256","aggregate layout",True)
 if (set(layout)!={"bank_size","inputs","inventory_contract","leaf_count","leaf_members_sha256","modules",
                   "prefixes","profile_bank_counts","schema","top_module"}
  or layout.get("schema")!=LAYOUT_SCHEMA or layout.get("leaf_count")!=13351
  or not isinstance(layout.get("inputs"),dict) or layout["inputs"].get("index")!={"bytes":reindex_output.stat().st_size,
     "path":str(reindex_output),"sha256":reindex["output_sha256"]}
  or layout["inputs"].get("inventory")!={"bytes":capacity_inventory.stat().st_size,"path":str(capacity_inventory),
     "sha256":bank["capacity_inventory_sha256"]}
  or not isinstance(layout.get("profile_bank_counts"),list) or not isinstance(layout.get("prefixes"),dict)
  or not isinstance(layout.get("top_module"),str) or not layout["top_module"]): raise ValueError("aggregate layout mismatch")
 layout_module_fields={"direct_import_count","direct_imports","file","kind","members","module","source_bytes",
                       "source_sha256","theorem"}
 if (not isinstance(layout["modules"],list) or not layout["modules"]
  or any(not isinstance(row,dict) or set(row)!=layout_module_fields for row in layout["modules"])):
  raise ValueError("aggregate layout module schema mismatch")
 aggregate_prefix=layout["prefixes"].get("aggregate_modules")
 if not isinstance(aggregate_prefix,str) or not aggregate_prefix: raise ValueError("aggregate prefix malformed")
 aggregate_root=repo/"proofs"/Path(*aggregate_prefix.split("."))
 if layout_path!=aggregate_root/"aggregate-layout.json": raise ValueError("aggregate layout root mismatch")
 safe(aggregate_root,"aggregate source root",kind="dir")
 aggregate_worktree=[]; top_rows=[]
 aggregate_sources={}
 for record in layout["modules"]:
  path=repo/("proofs/"+"/".join(record["module"].split("."))+".lean")
  if path!=aggregate_root/record["file"]: raise ValueError("aggregate module path mismatch")
  require(path,record["source_sha256"],"aggregate module source")
  if path.stat().st_size!=record["source_bytes"]: raise ValueError("aggregate module byte mismatch")
  aggregate_worktree.append({"repo_path":path.relative_to(repo).as_posix(),"bytes":path.stat().st_size,
                             "sha256":record["source_sha256"]})
  aggregate_sources[record["file"]]=path.read_text()
  if record["kind"]=="top-bank": top_rows.append(record)
 if len(top_rows)!=1 or layout["top_module"]!=top_rows[0]["module"]: raise ValueError("aggregate top module mismatch")
 layout_producer=repo/LAYOUT_PRODUCER; layout_spec=importlib.util.spec_from_file_location("h1_final_layout_contract",layout_producer)
 if layout_spec is None or layout_spec.loader is None: raise ValueError("layout producer cannot be loaded")
 layout_module=importlib.util.module_from_spec(layout_spec); sys.modules[layout_spec.name]=layout_module
 layout_spec.loader.exec_module(layout_module)
 layout_rows=layout_module.read_index(reindex_output); layout_module.validate_layout_manifest(layout,layout_rows,aggregate_sources)
 adapter_path,adapter=nested_receipt("adapter_receipt_path","adapter_receipt_sha256","adapter receipt")
 adapter_fields={"aggregate_layout_path","aggregate_layout_sha256","aggregate_source_root","aggregate_sources_identity_sha256",
  "capacity_index_path","capacity_index_sha256","capacity_reindex_receipt_path","capacity_reindex_receipt_sha256",
  "generator_sha256","generator_source","input_top_module","input_top_path","input_top_repo_path","input_top_sha256",
  "input_top_theorem","leaf_count","leaf_module_index_path","leaf_module_index_sha256","output_bytes","output_path",
  "output_sha256","output_source_module","output_theorem","repo","schema"}
 if (set(adapter)!=adapter_fields or adapter.get("schema")!=ADAPTER_SCHEMA or adapter.get("repo")!=str(repo)
  or adapter.get("leaf_count")!=13351 or adapter.get("aggregate_layout_path")!=str(layout_path)
  or adapter.get("aggregate_layout_sha256")!=post["aggregate_layout_sha256"]
  or adapter.get("capacity_reindex_receipt_path")!=str(reindex_path)
  or adapter.get("capacity_reindex_receipt_sha256")!=post["capacity_reindex_receipt_sha256"]
  or adapter.get("capacity_index_path")!=str(reindex_output) or adapter.get("capacity_index_sha256")!=reindex["output_sha256"]
  or adapter.get("leaf_module_index_path")!=post["leaf_module_index_path"]
  or adapter.get("leaf_module_index_sha256")!=post["leaf_module_index_sha256"]
  or adapter.get("output_source_module")!=MODULE or adapter.get("output_theorem")!=THEOREM
  or adapter.get("output_sha256")!=post["endpoint_source_sha256"]
  or adapter.get("aggregate_source_root")!=str(aggregate_root)
  or adapter.get("aggregate_sources_identity_sha256")!=hashlib.sha256(canonical(aggregate_worktree)).hexdigest()
  or adapter.get("input_top_module")!=top_rows[0]["module"]
  or adapter.get("input_top_path")!=str(aggregate_root/top_rows[0]["file"])
  or adapter.get("input_top_repo_path")!=(aggregate_root/top_rows[0]["file"]).relative_to(repo).as_posix()
  or adapter.get("input_top_sha256")!=top_rows[0]["source_sha256"]
  or adapter.get("input_top_theorem")!=top_rows[0]["theorem"]
  or adapter.get("output_path")!=str(repo/SOURCE) or adapter.get("output_bytes")!=(repo/SOURCE).stat().st_size
  or adapter.get("generator_source")!=ADAPTER_PRODUCER or adapter.get("generator_sha256")!=ADAPTER_PRODUCER_SHA256):
  raise ValueError("adapter receipt mismatch")
 leaf_path,leaf=nested_receipt("leaf_module_index_path","leaf_module_index_sha256","leaf module index")
 if (set(leaf)!={"capacity_index_sha256","leaf_count","modules","schema"} or leaf.get("schema")!=LEAF_SCHEMA
  or leaf.get("leaf_count")!=13351 or len(leaf.get("modules",[]))!=13351
  or leaf.get("capacity_index_sha256")!=reindex["output_sha256"]): raise ValueError("leaf module index mismatch")
 leaf_fields={"local_index","orbit","packed_lrat_sha256","profile","source_bytes","source_module","source_path","source_sha256"}
 leaf_expectations={}
 for evidence_row,module_row in zip(evidence["rows"],leaf["modules"],strict=True):
  prefix=layout.get("prefixes",{}).get("leaf_modules") if isinstance(layout.get("prefixes"),dict) else None
  expected_module=(f"{prefix}.Erdos85H1V2CertP{evidence_row['profile']}I{evidence_row['capacity_local_index']:05d}"
                   if isinstance(prefix,str) and prefix else None)
  expected_path=("proofs/"+"/".join(expected_module.split("."))+".lean") if expected_module else None
  expected_theorem=f"h1V2P{evidence_row['profile']}I{evidence_row['capacity_local_index']:05d}Checked"
  if (not isinstance(module_row,dict) or set(module_row)!=leaf_fields
   or (module_row["orbit"],module_row["profile"],module_row["local_index"],module_row["packed_lrat_sha256"])
      !=(evidence_row["tag"],evidence_row["profile"],evidence_row["capacity_local_index"],evidence_row["packed_sha256"])
   or module_row["source_module"]!=expected_module or evidence_row["leaf_repo_path"]!=expected_path
   or Path(module_row["source_path"])!=repo/evidence_row["leaf_repo_path"]
   or module_row["source_sha256"]!=evidence_row["leaf_source_sha256"]
   or module_row["source_bytes"]!=evidence_row["leaf_source_bytes"]
   or evidence_row["leaf_repo_path"] in leaf_expectations): raise ValueError("leaf module/evidence mismatch")
  safe(Path(module_row["source_path"]),"leaf source")
  if re.search(rf"\b{re.escape(expected_theorem)}\b",Path(module_row["source_path"]).read_text()) is None:
   raise ValueError("leaf theorem declaration missing")
  leaf_expectations[evidence_row["leaf_repo_path"]]=evidence_row
 compiled=cold.get("retained_generated_artifacts"); compiled_fields={"artifact_path","build_path","bytes","sha256"}
 if (not isinstance(compiled,list) or not compiled or any(not isinstance(row,dict) or set(row)!=compiled_fields
  or type(row["bytes"]) is not int or row["bytes"]<=0 or SHA.fullmatch(str(row["sha256"])) is None for row in compiled)):
  raise ValueError("compiled cone contract mismatch")
 cold_root=cold_path.parent; compiled_paths=[]
 for row in compiled:
  path=child(cold_root,row["artifact_path"],"compiled artifact"); require(path,row["sha256"],"compiled artifact")
  if path.stat().st_size!=row["bytes"]: raise ValueError("compiled artifact bytes mismatch")
  pins[str(path)]=row["sha256"]; compiled_paths.append(row["artifact_path"])
 if len(set(compiled_paths))!=len(compiled_paths): raise ValueError("compiled artifact duplicate")
 pending=[MODULE]; closure=set()
 while pending:
  module=pending.pop()
  if module in closure: continue
  source_path=repo/("proofs/"+"/".join(module.split("."))+".lean"); safe(source_path,"import closure source")
  closure.add(module)
  for line in source_path.read_text().splitlines():
   match=re.fullmatch(r"\s*import\s+(Proofs\.[A-Za-z0-9_'.]+)\s*",line)
   if match and match.group(1) not in closure: pending.append(match.group(1))
 generated_closure={module for module in closure if module.startswith("Proofs.Generated.")}
 compiled_identities=set(); compiled_build_paths=set()
 for row in compiled:
  build=PurePosixPath(row["build_path"])
  prefix=PurePosixPath(".lake/build/lib/lean")
  try: relative=build.relative_to(prefix)
  except ValueError as error: raise ValueError("compiled build path malformed") from error
  if relative.suffix not in (".olean",".ilean"): raise ValueError("compiled extension malformed")
  module=".".join(relative.with_suffix("").parts)
  expected_artifact="artifacts/generated/"+relative.as_posix()
  if module not in generated_closure or row["artifact_path"]!=expected_artifact:
   raise ValueError("compiled module/source mapping mismatch")
  if row["build_path"] in compiled_build_paths: raise ValueError("compiled build path duplicate")
  compiled_build_paths.add(row["build_path"]); compiled_identities.add((module,relative.suffix))
 expected_compiled={(module,suffix) for module in generated_closure for suffix in (".olean",".ilean")}
 if compiled_identities!=expected_compiled: raise ValueError("compiled Generated import closure mismatch")
 endpoint_rows=[row for row in compiled if row["build_path"]==cold.get("target_olean_build_path")]
 if (len(endpoint_rows)!=1 or endpoint_rows[0]["sha256"]!=cold.get("target_olean_sha256")
  or endpoint_rows[0]["bytes"]!=cold.get("target_olean_bytes")
  or endpoint_rows[0]["artifact_path"]!=cold.get("target_generated_artifact_path")):
  raise ValueError("endpoint compiled identity mismatch")
 legacy=child(cold_root,cold["target_olean_path"],"endpoint olean"); require(legacy,cold["target_olean_sha256"],"endpoint olean")
 if legacy.stat().st_size!=cold["target_olean_bytes"]: raise ValueError("endpoint olean bytes mismatch")
 pins[str(legacy)]=cold["target_olean_sha256"]
 project_sources=axiom.get("project_cone_source_identities")
 if (not isinstance(project_sources,list) or not project_sources): raise ValueError("project source identities missing")
 producer_pins={AXIOM_PRODUCER:AXIOM_PRODUCER_SHA256,COLD_PRODUCER:COLD_PRODUCER_SHA256,
                CACHE_PRODUCER:CACHE_PRODUCER_SHA256,POST_PRODUCER:POST_PRODUCER_SHA256,
                BANK_PRODUCER:BANK_PRODUCER_SHA256,REINDEX_PRODUCER:REINDEX_PRODUCER_SHA256,
                LAYOUT_PRODUCER:LAYOUT_PRODUCER_SHA256,ADAPTER_PRODUCER:ADAPTER_PRODUCER_SHA256,
                LEDGER_PRODUCER:LEDGER_PRODUCER_SHA256,FINAL_PRODUCER:sha(producer)}
 source_specs=[]
 for text,pin in producer_pins.items(): source_specs.append((text,pin,None,None))
 for helper in helpers:
  source_specs.append(("research/problems/erdos-85-wip-01/sat49/"+helper["source"],helper["sha256"],None,None))
 source_specs.append((snapshot_identity["path"],snapshot_identity["sha256"],snapshot_identity["blob_oid"],snapshot_identity["bytes"]))
 for item in controls: source_specs.append((item["path"],item["sha256"],item["blob_oid"],item["bytes"]))
 for key in ("adapter_source_identity","aggregate_layout_source_identity"):
  item=evidence[key]
  if (not isinstance(item,dict) or set(item)!={"blob_oid","bytes","repo_path","sha256"}
   or OID.fullmatch(str(item.get("blob_oid"))) is None or type(item.get("bytes")) is not int or item["bytes"]<=0
   or SHA.fullmatch(str(item.get("sha256"))) is None): raise ValueError("terminal source identity malformed")
  source_specs.append((item["repo_path"],item["sha256"],item["blob_oid"],item["bytes"]))
 audited_sources=axiom.get("audited_source_identities")
 if not isinstance(audited_sources,list) or not audited_sources: raise ValueError("audited source identities missing")
 for item in audited_sources:
  if (not isinstance(item,dict) or set(item)!={"blob_oid","bytes","path","sha256"}
   or OID.fullmatch(str(item["blob_oid"])) is None or type(item["bytes"]) is not int or item["bytes"]<=0):
   raise ValueError("audited source identity malformed")
  source_specs.append((item["path"],item["sha256"],item["blob_oid"],item["bytes"]))
 for item in project_sources:
  if (not isinstance(item,dict) or set(item)!={"blob_oid","bytes","path","sha256"}
   or OID.fullmatch(str(item["blob_oid"])) is None): raise ValueError("project source identity malformed")
  source_specs.append((item["path"],item["sha256"],item["blob_oid"],item["bytes"]))
 endpoint_item=next((item for item in project_sources if item["path"]==SOURCE),None)
 if endpoint_item is None or endpoint_item["sha256"]!=post["endpoint_source_sha256"]:
  raise ValueError("endpoint source identity missing")
 project_by_path={item["path"]:item for item in project_sources}
 if len(project_by_path)!=len(project_sources): raise ValueError("project source identity duplicate")
 cone_module_paths={"proofs/"+"/".join(module.split("."))+".lean" for module in theorem_modules.values()}
 if not cone_module_paths<=set(project_by_path): raise ValueError("cone module source coverage mismatch")
 for text,row in leaf_expectations.items():
  item=project_by_path.get(text)
  if (item is None or (item["blob_oid"],item["bytes"],item["sha256"])
      !=(row["leaf_blob_oid"],row["leaf_source_bytes"],row["leaf_source_sha256"])):
   raise ValueError("leaf/project source identity mismatch")
 for record in layout["modules"]:
  text="proofs/"+"/".join(record["module"].split("."))+".lean"
  item=project_by_path.get(text)
  if item is None or item["sha256"]!=record["source_sha256"] or item["bytes"]!=record["source_bytes"]:
   raise ValueError("aggregate/project source identity mismatch")
 adapter_identity=evidence["adapter_source_identity"]
 if (adapter_identity["repo_path"]!=SOURCE or adapter_identity["sha256"]!=endpoint_item["sha256"]
  or adapter_identity["bytes"]!=endpoint_item["bytes"] or adapter_identity["blob_oid"]!=endpoint_item["blob_oid"]):
  raise ValueError("adapter endpoint source identity mismatch")
 leaf_identity_rows=[{"blob_oid":row["leaf_blob_oid"],"bytes":row["leaf_source_bytes"],
  "repo_path":row["leaf_repo_path"],"sha256":row["leaf_source_sha256"]} for row in evidence["rows"]]
 aggregate_identity_rows=[evidence["aggregate_layout_source_identity"]]
 for record in layout["modules"]:
  text="proofs/"+"/".join(record["module"].split("."))+".lean"
  item=project_by_path[text]
  aggregate_identity_rows.append({"blob_oid":item["blob_oid"],"bytes":item["bytes"],"repo_path":text,
                                  "sha256":item["sha256"]})
 leaf_tree=hashlib.sha256(canonical(leaf_identity_rows)).hexdigest()
 aggregate_tree=hashlib.sha256(canonical(aggregate_identity_rows)).hexdigest()
 generated_tree=hashlib.sha256(canonical([*leaf_identity_rows,*aggregate_identity_rows,adapter_identity])).hexdigest()
 if (evidence.get("leaf_tree_identity_sha256")!=leaf_tree
  or evidence.get("aggregate_tree_identity_sha256")!=aggregate_tree
  or evidence.get("generated_tree_identity_sha256")!=generated_tree
  or post.get("generated_tree_identity_sha256")!=generated_tree or cold.get("generated_tree_identity_sha256")!=generated_tree):
  raise ValueError("generated source tree identity mismatch")
 unique_paths=[]; expected_oids={}; expected_bytes={}; expected_pins={}
 for text,pin,blob,size in source_specs:
  if text in unique_paths:
   if (expected_pins[text]!=pin or blob is not None and expected_oids[text] not in (None,blob)
    or size is not None and expected_bytes[text] not in (None,size)):
    raise ValueError("source identity mixing")
   if blob is not None: expected_oids[text]=blob
   if size is not None: expected_bytes[text]=size
   continue
  rel(text,"source path"); path=repo/Path(*PurePosixPath(text).parts); require(path,pin,"committed source")
  if size is not None and path.stat().st_size!=size: raise ValueError("committed source byte mismatch")
  if path.suffix==".lean" and re.search(rb"\b(?:sorry|admit)\b",path.read_bytes().lower()):
   raise ValueError("sorry/admit in committed source")
  pins[str(path)]=pin; unique_paths.append(text); expected_pins[text]=pin
  expected_oids[text]=blob; expected_bytes[text]=size
 git=Path(snapshot["git_path"]); require(git,snapshot["git_sha256"],"Git executable"); pins[str(git)]=snapshot["git_sha256"]
 commit_oids=run_git(runner,"source_commit_oids",[str(git),"-C",str(repo),"rev-parse",*[f"{source_commit}:{p}" for p in unique_paths]],repo).decode().splitlines()
 work_oids=run_git(runner,"source_worktree_oids",[str(git),"-C",str(repo),"hash-object","--",*unique_paths],repo).decode().splitlines()
 if (len(commit_oids)!=len(unique_paths) or commit_oids!=work_oids or any(OID.fullmatch(x) is None for x in commit_oids)):
  raise ValueError("committed source Git identity mismatch")
 for text,oid in zip(unique_paths,commit_oids,strict=True):
  if expected_oids[text] is not None and expected_oids[text]!=oid: raise ValueError("project source blob identity mismatch")
 source_oid_by_path=dict(zip(unique_paths,commit_oids,strict=True))
 metadata_pins={text:(Path(text).stat().st_size,os.stat(Path(text),follow_symlinks=False).st_dev,
                           os.stat(Path(text),follow_symlinks=False).st_ino) for text in pins}
 stage=Path(tempfile.mkdtemp(prefix=".h1-wrapper-final-stage.",dir=output.parent))
 try:
  publication=stage/"publication"; publication.mkdir()
  copies=[(axiom_receipt,"evidence/receipts/axiom.json"),(cold_path,"evidence/receipts/cold.json"),
   (snapshot_path,"evidence/receipts/cache-snapshot.json"),(cache_path,"evidence/cache/cache-manifest.json"),
   (post_path,"evidence/receipts/post-module.json"),(evidence_path,"evidence/post/leaf-evidence.json"),
   (bank_path,"evidence/post-chain/bank-receipt.json"),(payload_path,"evidence/post-chain/payload-index.json"),
   (replay_audit_path,"evidence/post-chain/replay-audit.json"),
   (capacity_inventory,"evidence/post-chain/capacity-inventory.tsv"),
   (ledger_receipt_path,"evidence/post-chain/selected-ledger-receipt.json"),
   (ledger_snapshot_path,"evidence/post-chain/selected-ledgers.json"),
   (source_index_path,"evidence/post-chain/source-index.tsv"),(bank_tool_path,"evidence/post-chain/toolchain.json"),
   (reindex_output,"evidence/post-chain/capacity-index.tsv"),
   (coverage_path,"evidence/post-chain/coverage/receipt.json"),
   (coverage_root/"counts.json","evidence/post-chain/coverage/counts.json"),
   (coverage_root/"coverage.tsv","evidence/post-chain/coverage/coverage.tsv"),
   (coverage_root/"inventory_universe_diff.tsv","evidence/post-chain/coverage/inventory_universe_diff.tsv"),
   (reindex_path,"evidence/post-chain/capacity-reindex-receipt.json"),
   (layout_path,"evidence/post-chain/aggregate-layout.json"),
   (adapter_path,"evidence/post-chain/adapter-receipt.json"),(leaf_path,"evidence/post-chain/leaf-module-index.json"),
   (legacy,"evidence/endpoint/Erdos85OrderFortyNineOneHighCertificates.olean"),
   (repo/SOURCE,"evidence/endpoint/Erdos85OrderFortyNineOneHighCertificates.lean")]
  copies += [(child(axiom_root,row["path"],"axiom artifact"),"evidence/"+row["path"]) for row in artifacts]
  for prefix,document,root in (("axiom",axiom,axiom_root),("cold",cold,cold_path.parent)):
   for kind,record in document["commands"].items():
    for stream in ("stdout","stderr"):
     copies.append((child(root,record[f"{stream}_path"],f"{prefix} command log"),
                    f"evidence/{prefix}-command-logs/{kind}.{stream}"))
  retained=[]
  for source,text in copies:
   destination=publication/Path(*PurePosixPath(text).parts); destination.parent.mkdir(parents=True,exist_ok=True)
   source_pin=sha(source); source_bytes=source.stat().st_size; shutil.copyfile(source,destination)
   require(destination,source_pin,"retained evidence")
   if destination.stat().st_size!=source_bytes: raise ValueError("retained evidence bytes mismatch")
   retained.append({"bytes":source_bytes,"path":text,"sha256":source_pin})
  projection={"consumer_argument":"h1","schema":PROJECTION_SCHEMA,"source_module":MODULE,
   "source_sha256":endpoint_item["sha256"],"theorem":THEOREM}
  projection_path="evidence/consumer/h1-provenance.json"
  projection_destination=publication/projection_path
  projection_destination.parent.mkdir(parents=True,exist_ok=True)
  projection_raw=canonical(projection); projection_destination.write_bytes(projection_raw)
  projection_pin=hashlib.sha256(projection_raw).hexdigest()
  retained.append({"bytes":len(projection_raw),"path":projection_path,"sha256":projection_pin})
  retained.sort(key=lambda x:x["path"])
  retained_paths=[row["path"] for row in retained]
  if len(retained_paths)!=len(set(retained_paths)): raise ValueError("retained destination collision")
  endpoint_source_path="evidence/endpoint/Erdos85OrderFortyNineOneHighCertificates.lean"
  endpoint_olean_path="evidence/endpoint/Erdos85OrderFortyNineOneHighCertificates.olean"
  endpoint={"generated_tree_identity_sha256":post["generated_tree_identity_sha256"],"module":MODULE,
   "olean_bytes":cold["target_olean_bytes"],"olean_path":endpoint_olean_path,
   "olean_sha256":cold["target_olean_sha256"],"original_source_path":SOURCE,
   "source_blob_oid":source_oid_by_path[SOURCE],"source_bytes":endpoint_item["bytes"],"source_path":endpoint_source_path,
   "source_sha256":endpoint_item["sha256"],"theorem":THEOREM}
  producer_identity={"blob_oid":source_oid_by_path[FINAL_PRODUCER],"bytes":producer.stat().st_size,"commit":source_commit,
   "path":FINAL_PRODUCER,"sha256":pins[str(producer)]}
  def retained_identity(path,pin,schema):
   row=next(item for item in retained if item["path"]==path)
   if row["sha256"]!=pin: raise ValueError("retained upstream identity mismatch")
   return {"bytes":row["bytes"],"path":path,"schema":schema,"sha256":pin}
  receipt={"artifacts":retained,"audit_identity":{"foundational_axioms":FOUNDATIONAL,
   "native_root_count":axiom["native_root_count"],"producer_sha256":AXIOM_PRODUCER_SHA256,
   "project_cone_identity_sha256":hashlib.sha256(canonical(project_sources)).hexdigest(),"status":"PASS",
   "theorem_count":axiom["theorem_count"]},"cache_identity_sha256":cache["identity_sha256"],
   "compiled_cone_identity_sha256":hashlib.sha256(canonical(compiled)).hexdigest(),
   "compiled_cone_size":len(compiled),"control_identities":snapshot["control_files"],"endpoint_identity":endpoint,
   "consumer_projection_identity":{"bytes":len(projection_raw),"path":projection_path,
    "schema":PROJECTION_SCHEMA,"sha256":projection_pin},"image":IMAGE,"producer_identity":producer_identity,
   "producer_path":str(repo/FINAL_PRODUCER),"producer_sha256":pins[str(producer)],"repo":str(repo),
   "review_id":post["review_id"],"schema":SCHEMA,"source_commit":source_commit,
   "terminal_capacity":{"adapter_receipt_sha256":post["adapter_receipt_sha256"],
    "aggregate_layout_sha256":post["aggregate_layout_sha256"],"bank_receipt_sha256":post["bank_receipt_sha256"],
    "capacity_reindex_receipt_sha256":post["capacity_reindex_receipt_sha256"],"evidence_sha256":post["evidence_sha256"],
    "leaf_count":13351,"leaf_module_index_sha256":post["leaf_module_index_sha256"],
    "payload_identity_sha256":bank["payload_identity_sha256"],"payload_index_sha256":bank["payload_index_sha256"],
    "coverage_receipt_sha256":bank["coverage_receipt_sha256"],"profile_counts":PROFILE_COUNTS,
    "replay_audit_sha256":bank["replay_audit_sha256"],"status":"PASS",
    "terminal_counts":TERMINAL_COUNTS,
    "replay_evidence_identity_sha256":replay_audit["replay_evidence_identity_sha256"]},
   "tool_identities":axiom["tool_identities"],"upstream_receipts":{
    "axiom":retained_identity("evidence/receipts/axiom.json",axiom_pin,AXIOM_SCHEMA),
    "cache_manifest":retained_identity("evidence/cache/cache-manifest.json",axiom["cache_manifest_sha256"],CACHE_SCHEMA),
    "cache_snapshot":retained_identity("evidence/receipts/cache-snapshot.json",axiom["cache_snapshot_receipt_sha256"],CACHE_RECEIPT_SCHEMA),
    "cold":retained_identity("evidence/receipts/cold.json",axiom["cold_receipt_sha256"],COLD_SCHEMA),
    "post_module":retained_identity("evidence/receipts/post-module.json",cold["post_module_receipt_sha256"],POST_SCHEMA)}}
  if before_receipt: before_receipt()
  for text,pin in pins.items():
   path=Path(text); require(path,pin,"input drift before receipt"); info=os.stat(path,follow_symlinks=False)
   if (info.st_size,info.st_dev,info.st_ino)!=metadata_pins[text]: raise ValueError("input replacement before receipt")
  parent_info=os.stat(output.parent,follow_symlinks=False)
  if (parent_info.st_dev,parent_info.st_ino)!=output_parent_pin: raise ValueError("output parent replacement")
  expected=retained
  observed_files,observed_dirs=scan(publication,publication)
  expected_dirs=sorted({PurePosixPath(row["path"]).parent.as_posix() for row in retained}
   | {parent.as_posix() for row in retained for parent in PurePosixPath(row["path"]).parents
      if parent.as_posix() not in (".","")})
  if observed_files!=expected or observed_dirs!=expected_dirs: raise ValueError("final evidence tree drift")
  receipt_path=publication/"receipt.json"; receipt_raw=canonical(receipt)
  with receipt_path.open("xb") as stream:
   stream.write(receipt_raw); stream.flush(); os.fsync(stream.fileno())
  final_files,final_dirs=scan(publication,publication)
  final_expected=sorted([*retained,{"bytes":len(receipt_raw),"path":"receipt.json",
                                    "sha256":hashlib.sha256(receipt_raw).hexdigest()}],key=lambda x:x["path"])
  if final_files!=final_expected or final_dirs!=expected_dirs: raise ValueError("final publication tree drift")
  for path in publication.rglob("*"):
   if path.is_file():
    with path.open("rb") as stream: os.fsync(stream.fileno())
  for path in sorted((x for x in publication.rglob("*") if x.is_dir()),key=lambda x:len(x.parts),reverse=True)+[publication]:
   fd=os.open(path,os.O_RDONLY)
   try: os.fsync(fd)
   finally: os.close(fd)
  if output.exists() or output.is_symlink(): raise ValueError("output appeared")
  if before_publish: before_publish()
  rename_noreplace(publication,output); fd=os.open(output.parent,os.O_RDONLY)
  try: os.fsync(fd)
  finally: os.close(fd)
  return receipt
 except Exception:
  if stage.exists(): shutil.rmtree(stage)
  raise
 finally:
  if stage.exists(): shutil.rmtree(stage)

def main():
 parser=argparse.ArgumentParser(description=__doc__); parser.add_argument("--repo",type=Path,required=True)
 parser.add_argument("--axiom-receipt",type=Path,required=True); parser.add_argument("--axiom-receipt-sha256",required=True)
 parser.add_argument("--output",type=Path,required=True); args=parser.parse_args()
 def runner(kind,argv,cwd):
  result=__import__("subprocess").run(argv,cwd=cwd,stdout=__import__("subprocess").PIPE,stderr=__import__("subprocess").PIPE)
  return {"rc":result.returncode,"stdout":result.stdout,"stderr":result.stderr}
 build(args.repo,args.axiom_receipt,args.axiom_receipt_sha256,args.output,runner)
if __name__=="__main__": main()
