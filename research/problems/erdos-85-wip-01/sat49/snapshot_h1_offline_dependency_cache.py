#!/usr/bin/env python3
"""Snapshot a reviewed, package-authenticated Lake cache for offline H1 builds."""
from __future__ import annotations
import argparse, hashlib, json, os, re, shutil, subprocess, tempfile
from pathlib import Path, PurePosixPath

SCHEMA="erdos85-h1-offline-dependency-cache-v1"
RECEIPT_SCHEMA="erdos85-h1-offline-dependency-cache-snapshot-receipt-v1"
COMMIT=re.compile(r"[0-9a-f]{40}"); SHA=re.compile(r"[0-9a-f]{64}")
CONTROL_PATHS=("proofs/lean-toolchain","proofs/lakefile.toml","proofs/lake-manifest.json")
MANIFEST_FIELDS={"fixedToolchain","lakeDir","name","packages","packagesDir","version"}
PACKAGE_FIELDS={"configFile","inherited","inputRev","manifestFile","name","rev","scope","subDir","type","url"}

def canonical(value):
 return (json.dumps(value,ensure_ascii=True,allow_nan=False,sort_keys=True,separators=(",",":"))+"\n").encode("ascii")
def sha(path):
 digest=hashlib.sha256()
 with path.open("rb") as stream:
  for block in iter(lambda:stream.read(1<<20),b""): digest.update(block)
 return digest.hexdigest()
def safe(path,label,kind="file",absent=False):
 if not path.is_absolute() or path!=path.resolve(strict=False): raise ValueError(f"{label} is not canonical absolute")
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
def rel(text,label):
 if not isinstance(text,str) or not text or "\\" in text: raise ValueError(f"{label} path malformed")
 path=PurePosixPath(text)
 if path.is_absolute() or path.as_posix()!=text or any(x in ("",".","..") for x in path.parts):
  raise ValueError(f"{label} path malformed")
 return path
def normalize_url(value):
 if not isinstance(value,str): raise ValueError("package remote URL malformed")
 match=re.fullmatch(r"(?:https://github\.com/|git@github\.com:)([^/]+)/([^/]+?)(?:\.git)?/?",value)
 if match is None: raise ValueError("package remote URL is not canonical GitHub remote")
 return f"github.com/{match.group(1).lower()}/{match.group(2).lower()}"
def run(runner,kind,argv,cwd):
 result=runner(kind,argv,cwd)
 if (not isinstance(result,dict) or set(result)!={"rc","stdout","stderr"} or result["rc"]!=0
   or not isinstance(result["stdout"],bytes) or not isinstance(result["stderr"],bytes) or result["stderr"]):
  raise ValueError(f"{kind} Git command failed/malformed")
 return result["stdout"]
def enumerate_files(root,proofs):
 entries=[]; inodes=set()
 for current,dirs,files in os.walk(root,followlinks=False):
  base=Path(current)
  for name in dirs:
   path=base/name
   if path.is_symlink(): raise ValueError("cache directory symlink forbidden")
  for name in files:
   path=base/name
   if path.is_symlink() or not path.is_file(): raise ValueError("cache special/symlink file forbidden")
   stat=path.stat(); inode=(stat.st_dev,stat.st_ino)
   if stat.st_nlink!=1 or inode in inodes: raise ValueError("cache hardlink/alias forbidden")
   inodes.add(inode)
   text=path.relative_to(proofs).as_posix(); rel(text,"cache entry")
   lower=PurePosixPath(text)
   prefix=(".lake","build","lib","lean","Proofs","Generated")
   if lower.parts[:len(prefix)]==prefix and lower.suffix in (".olean",".ilean"):
    raise ValueError("cache contains Generated Lean artifact")
   entries.append({"bytes":path.stat().st_size,"path":text,"sha256":sha(path)})
 entries.sort(key=lambda item:item["path"])
 if len({item["path"] for item in entries})!=len(entries): raise ValueError("duplicate cache path")
 return entries
def fsync_tree(root):
 for path in root.rglob("*"):
  if path.is_file():
   with path.open("rb") as stream: os.fsync(stream.fileno())
 for path in sorted((p for p in root.rglob("*") if p.is_dir()),key=lambda p:len(p.parts),reverse=True)+[root]:
  fd=os.open(path,os.O_RDONLY)
  try: os.fsync(fd)
  finally: os.close(fd)

def build(repo,source_commit,cache_root,git_path,git_sha256,output,runner,before_receipt=None):
 producer=Path(__file__).resolve(); safe(repo,"repo",kind="dir"); safe(cache_root,"cache root",kind="dir")
 require(git_path,git_sha256,"git executable")
 safe(output,"output",absent=True)
 try: output.relative_to(cache_root)
 except ValueError: pass
 else: raise ValueError("output must be outside cache root")
 if COMMIT.fullmatch(source_commit) is None: raise ValueError("reviewed commit malformed")
 proofs=repo/"proofs"
 if cache_root!=proofs/".lake": raise ValueError("cache root is not canonical repo proofs/.lake")
 git=str(git_path)
 head=run(runner,"repo_head",[git,"-C",str(repo),"rev-parse","HEAD"],repo).decode().strip()
 status=run(runner,"repo_status",[git,"-C",str(repo),"status","--porcelain=v1","--untracked-files=all"],repo)
 if head!=source_commit or status: raise ValueError("repo commit/status mismatch")
 commit_oids=run(runner,"control_commit_oids",[git,"-C",str(repo),"rev-parse",
  *[f"{source_commit}:{path}" for path in CONTROL_PATHS]],repo).decode().splitlines()
 work_oids=run(runner,"control_worktree_oids",[git,"-C",str(repo),"hash-object","--",*CONTROL_PATHS],repo).decode().splitlines()
 if len(commit_oids)!=3 or commit_oids!=work_oids or any(COMMIT.fullmatch(x) is None for x in commit_oids):
  raise ValueError("reviewed control Git identity mismatch")
 controls=[]
 for text,oid in zip(CONTROL_PATHS,commit_oids,strict=True):
  path=repo/Path(*PurePosixPath(text).parts); safe(path,text)
  controls.append({"blob_oid":oid,"bytes":path.stat().st_size,"path":text,"sha256":sha(path)})
 manifest_path=repo/"proofs/lake-manifest.json"; raw=manifest_path.read_bytes()
 manifest=json.loads(raw)
 if (not isinstance(manifest,dict) or set(manifest)!=MANIFEST_FIELDS or manifest.get("version")!="1.2.0"
  or manifest.get("packagesDir")!=".lake/packages" or manifest.get("lakeDir")!=".lake"
  or manifest.get("name")!="proofs" or not isinstance(manifest.get("packages"),list)
  or any(not isinstance(item,dict) or set(item)!=PACKAGE_FIELDS for item in manifest["packages"])):
  raise ValueError("lake manifest closed schema mismatch")
 packages=[]; names=set(); remotes=set()
 for item in manifest["packages"]:
  name=item["name"]
  if (not isinstance(name,str) or re.fullmatch(r"[A-Za-z][A-Za-z0-9_-]*",name) is None or name in names
   or item["type"]!="git" or COMMIT.fullmatch(str(item["rev"])) is None or item["subDir"] is not None):
   raise ValueError("lake package record mismatch")
  names.add(name); package=cache_root/"packages"/name; safe(package,f"package {name}",kind="dir")
  phead=run(runner,f"package_head:{name}",[git,"-C",str(package),"rev-parse","HEAD"],repo).decode().strip()
  pstatus=run(runner,f"package_status:{name}",[git,"-C",str(package),"status","--porcelain=v1","--untracked-files=all"],repo)
  remote=run(runner,f"package_remote:{name}",[git,"-C",str(package),"remote","get-url","origin"],repo).decode().strip()
  normalized=normalize_url(remote)
  if phead!=item["rev"] or pstatus or normalized!=normalize_url(item["url"]) or normalized in remotes:
   raise ValueError(f"package {name} revision/status/remote mismatch")
  remotes.add(normalized)
  packages.append({"head":phead,"manifest_url":item["url"],"name":name,"normalized_remote":normalize_url(remote),
                   "path":str(package),"rev":item["rev"]})
 entries=enumerate_files(cache_root,proofs)
 by_package={name:[entry for entry in entries if PurePosixPath(entry["path"]).parts[:3]==(".lake","packages",name)]
             for name in names}
 for package in packages:
  package["source_identity_sha256"]=hashlib.sha256(canonical(by_package[package["name"]])).hexdigest()
 pins={str(producer):sha(producer),str(git_path):git_sha256,
       **{str(repo/item["path"]):item["sha256"] for item in controls},
       **{str(proofs/Path(*PurePosixPath(item["path"]).parts)):item["sha256"] for item in entries}}
 with tempfile.TemporaryDirectory(prefix=".h1-cache-snapshot-",dir=output.parent) as raw_stage:
  stage=Path(raw_stage); publication=stage/"publication"; snapshot=publication/"cache"; snapshot.mkdir(parents=True)
  for item in entries:
   source=proofs/Path(*PurePosixPath(item["path"]).parts); destination=snapshot/Path(*PurePosixPath(item["path"]).parts)
   destination.parent.mkdir(parents=True,exist_ok=True); shutil.copyfile(source,destination)
   require(destination,item["sha256"],"copied cache entry")
   if destination.stat().st_size!=item["bytes"]: raise ValueError("copied cache byte mismatch")
  output_entries=[{**item} for item in entries]
  cache_manifest={"entries":output_entries,"identity_sha256":hashlib.sha256(canonical(output_entries)).hexdigest(),
                  "root":str(output/"cache"),"schema":SCHEMA}
  manifest_raw=canonical(cache_manifest); (publication/"cache-manifest.json").write_bytes(manifest_raw)
  if before_receipt: before_receipt()
  for path,pin in pins.items(): require(Path(path),pin,"input drift before receipt")
  if enumerate_files(cache_root,proofs)!=entries: raise ValueError("source cache file set drift before receipt")
  if enumerate_files(snapshot,snapshot)!=entries: raise ValueError("snapshot cache file set drift before receipt")
  final_head=run(runner,"repo_head_final",[git,"-C",str(repo),"rev-parse","HEAD"],repo).decode().strip()
  final_status=run(runner,"repo_status_final",[git,"-C",str(repo),"status","--porcelain=v1","--untracked-files=all"],repo)
  if final_head!=source_commit or final_status: raise ValueError("repo drift before receipt")
  for package in packages:
   name=package["name"]; path=Path(package["path"])
   final_head=run(runner,f"package_head_final:{name}",[git,"-C",str(path),"rev-parse","HEAD"],repo).decode().strip()
   final_status=run(runner,f"package_status_final:{name}",[git,"-C",str(path),"status","--porcelain=v1","--untracked-files=all"],repo)
   final_remote=run(runner,f"package_remote_final:{name}",[git,"-C",str(path),"remote","get-url","origin"],repo).decode().strip()
   if final_head!=package["rev"] or final_status or normalize_url(final_remote)!=package["normalized_remote"]:
    raise ValueError("package drift before receipt")
  for item in entries:
   destination=snapshot/Path(*PurePosixPath(item["path"]).parts)
   require(destination,item["sha256"],"snapshot drift");
   if destination.stat().st_size!=item["bytes"]: raise ValueError("snapshot byte drift")
  receipt={"cache_manifest_path":"cache-manifest.json","cache_manifest_sha256":hashlib.sha256(manifest_raw).hexdigest(),
   "control_files":controls,"entry_count":len(entries),"package_count":len(packages),"packages":packages,
   "producer_path":str(producer),"producer_sha256":pins[str(producer)],"repo":str(repo),
   "git_path":str(git_path),"git_sha256":git_sha256,
   "schema":RECEIPT_SCHEMA,"source_commit":source_commit}
  receipt_raw=canonical(receipt); (publication/"receipt.json").write_bytes(receipt_raw)
  if (publication/"cache-manifest.json").read_bytes()!=manifest_raw or (publication/"receipt.json").read_bytes()!=receipt_raw:
   raise ValueError("nested output drift")
  fsync_tree(publication)
  if output.exists() or output.is_symlink(): raise ValueError("output appeared")
  publication.rename(output); fd=os.open(output.parent,os.O_RDONLY)
  try: os.fsync(fd)
  finally: os.close(fd)

def main():
 parser=argparse.ArgumentParser(description=__doc__); parser.add_argument("--repo",type=Path,required=True)
 parser.add_argument("--source-commit",required=True); parser.add_argument("--cache-root",type=Path,required=True)
 parser.add_argument("--git-path",type=Path,required=True); parser.add_argument("--git-sha256",required=True)
 parser.add_argument("--output",type=Path,required=True); args=parser.parse_args()
 def runner(kind,argv,cwd):
  result=subprocess.run(argv,cwd=cwd,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
  return {"rc":result.returncode,"stdout":result.stdout,"stderr":result.stderr}
 build(args.repo,args.source_commit,args.cache_root,args.git_path,args.git_sha256,args.output,runner)
if __name__=="__main__": main()
