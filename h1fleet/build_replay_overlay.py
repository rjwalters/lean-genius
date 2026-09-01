#!/usr/bin/env python3
"""Publish a package-authenticated, self-contained H1 `.olean` import root."""
from __future__ import annotations
import argparse, hashlib, json, os, re, shutil, subprocess, tempfile
from pathlib import Path, PurePosixPath
from typing import Callable

SCHEMA="erdos85-h1-replay-complete-olean-overlay-v1"
RECEIPT_SCHEMA="erdos85-h1-replay-complete-olean-overlay-receipt-v1"
IMPORT_EXTENSIONS=(".ir",".olean",".olean.private",".olean.server")
CONTROL_PATHS=("proofs/lean-toolchain","proofs/lakefile.toml","proofs/lake-manifest.json")
MANIFEST_FIELDS={"fixedToolchain","lakeDir","name","packages","packagesDir","version"}
PACKAGE_FIELDS={"configFile","inherited","inputRev","manifestFile","name","rev","scope","subDir","type","url"}
COMMIT=re.compile(r"[0-9a-f]{40}"); SHA=re.compile(r"[0-9a-f]{64}")
class OverlayError(ValueError): pass
def canonical(value): return (json.dumps(value,ensure_ascii=True,allow_nan=False,sort_keys=True,separators=(",",":"))+"\n").encode("ascii")
def sha256_file(path):
 d=hashlib.sha256()
 with path.open("rb") as stream:
  for block in iter(lambda:stream.read(1<<20),b""): d.update(block)
 return d.hexdigest()
def safe(path,label,kind="file",absent=False):
 if not path.is_absolute() or path!=path.resolve(strict=False): raise OverlayError(f"{label} is not canonical absolute")
 current=path if path.exists() else path.parent
 while True:
  if current.is_symlink(): raise OverlayError(f"{label} has symlink ancestry")
  if current==current.parent: break
  current=current.parent
 if absent:
  if path.exists() or path.is_symlink() or not path.parent.is_dir(): raise OverlayError(f"{label} must be absent")
 elif kind=="file" and (path.is_symlink() or not path.is_file()): raise OverlayError(f"{label} is not regular file")
 elif kind=="dir" and (path.is_symlink() or not path.is_dir()): raise OverlayError(f"{label} is not directory")
def require(path,pin,label):
 safe(path,label)
 if SHA.fullmatch(str(pin)) is None or sha256_file(path)!=pin: raise OverlayError(f"{label} hash mismatch")
def rel(text,label):
 if not isinstance(text,str) or not text or "\\" in text: raise OverlayError(f"{label} path malformed")
 path=PurePosixPath(text)
 if path.is_absolute() or path.as_posix()!=text or any(x in ("",".","..") for x in path.parts): raise OverlayError(f"{label} path malformed")
 return path
def normalize_url(value):
 if not isinstance(value,str): raise OverlayError("package remote URL malformed")
 match=re.fullmatch(r"(?:https://github\.com/|git@github\.com:)([^/]+)/([^/]+?)(?:\.git)?/?",value)
 if match is None: raise OverlayError("package remote is not canonical GitHub URL")
 return f"github.com/{match.group(1).lower()}/{match.group(2).lower()}"
def run(runner,kind,argv,cwd):
 result=runner(kind,argv,cwd)
 if (not isinstance(result,dict) or set(result)!={"rc","stdout","stderr"} or result["rc"]!=0
  or not isinstance(result["stdout"],bytes) or not isinstance(result["stderr"],bytes) or result["stderr"]):
  raise OverlayError(f"{kind} Git command failed/malformed")
 return result["stdout"]
def read_selection(path,pin):
 require(path,pin,"reviewed project overlay manifest"); result={}
 for number,line in enumerate(path.read_text().splitlines(),1):
  fields=line.split("\t")
  if len(fields)!=2 or SHA.fullmatch(fields[0]) is None: raise OverlayError(f"project manifest line {number} malformed")
  name=rel(fields[1],"project overlay entry").as_posix()
  if not name.endswith(".olean") or name.startswith("Proofs/Generated/") or name in result: raise OverlayError("forbidden/duplicate project overlay entry")
  result[name]=fields[0]
 if not result: raise OverlayError("project overlay selection empty")
 return result
def scan(root,origin,selected=None):
 safe(root,f"{origin} root",kind="dir"); rows=[]; inodes=set()
 for current,dirs,files in os.walk(root,followlinks=False):
  base=Path(current)
  for name in dirs:
   path=base/name
   if path.is_symlink() or not path.is_dir(): raise OverlayError(f"{origin} special/symlink directory")
  for name in files:
   path=base/name
   if path.is_symlink() or not path.is_file(): raise OverlayError(f"{origin} special/symlink file")
   stat=path.stat(); inode=(stat.st_dev,stat.st_ino)
   if stat.st_nlink!=1 or inode in inodes: raise OverlayError(f"{origin} hardlink/alias")
   inodes.add(inode); relative=path.relative_to(root).as_posix(); rel(relative,f"{origin} entry")
   # Lean 4.31 splits importable module data among `.olean`, `.olean.server`, and
   # `.olean.private`; the loader only discovers `.private` after `.server` exists.
   # Direct compilation also imports interpreter data from `.ir`.
   # `.ilean`, traces, and build hashes are not import inputs.
   if not any(relative.endswith(extension) for extension in IMPORT_EXTENSIONS): continue
   selected_path=relative
   if selected is not None and (relative.endswith(".olean.private") or relative.endswith(".olean.server")):
    selected_path=relative.rsplit(".",1)[0]
   elif selected is not None and relative.endswith(".ir"):
    selected_path=relative.removesuffix(".ir")+".olean"
   if selected is not None and selected_path not in selected: continue
   digest=sha256_file(path)
   if selected is not None and relative in selected and selected[relative]!=digest: raise OverlayError(f"project overlay hash mismatch: {relative}")
   rows.append({"bytes":stat.st_size,"origin":origin,"path":relative,"sha256":digest,"source":str(path)})
 rows.sort(key=lambda row:row["path"])
 if selected is not None and not set(selected).issubset(row["path"] for row in rows): raise OverlayError("project overlay census missing entries")
 return rows
def fsync_tree(root):
 for path in root.rglob("*"):
  if path.is_file():
   with path.open("rb") as stream: os.fsync(stream.fileno())
 for path in sorted((x for x in root.rglob("*") if x.is_dir()),key=lambda x:len(x.parts),reverse=True)+[root]:
  fd=os.open(path,os.O_RDONLY)
  try: os.fsync(fd)
  finally: os.close(fd)
def verify_tree(root,manifest):
 entries=manifest.get("entries")
 if (set(manifest)!={"entry_count","entries","identity_sha256","included_extensions","schema"}
 or manifest.get("schema")!=SCHEMA or manifest.get("included_extensions")!=list(IMPORT_EXTENSIONS)
  or not isinstance(entries,list) or manifest.get("entry_count")!=len(entries)
  or manifest.get("identity_sha256")!=hashlib.sha256(canonical(entries)).hexdigest()): raise OverlayError("overlay manifest exact schema mismatch")
 actual=[]
 for current,dirs,files in os.walk(root,followlinks=False):
  base=Path(current)
  if any((base/name).is_symlink() for name in dirs): raise OverlayError("overlay directory symlink")
  for name in files:
   path=base/name
   relative=path.relative_to(root).as_posix()
   if path.is_symlink() or not path.is_file() or not any(relative.endswith(extension) for extension in IMPORT_EXTENSIONS): raise OverlayError("overlay non-import-data/special file")
   actual.append(relative)
 expected=[]
 for row in entries:
  if not isinstance(row,dict) or set(row)!={"bytes","path","sha256"} or SHA.fullmatch(str(row.get("sha256"))) is None: raise OverlayError("overlay row malformed")
  rel(row["path"],"overlay entry"); path=root/row["path"]
  if path.is_symlink() or not path.is_file() or path.stat().st_size!=row["bytes"] or sha256_file(path)!=row["sha256"]: raise OverlayError(f"overlay identity mismatch: {row['path']}")
  expected.append(row["path"])
 if expected!=sorted(set(expected)) or sorted(actual)!=expected: raise OverlayError("overlay census differs from manifest")
 return len(entries)
def verify(publication):
 safe(publication,"publication",kind="dir")
 if sorted(x.name for x in publication.iterdir())!=["manifest.json","overlay","receipt.json"]: raise OverlayError("publication file set mismatch")
 try: manifest=json.loads((publication/"manifest.json").read_text())
 except json.JSONDecodeError as error: raise OverlayError("manifest malformed JSON") from error
 return verify_tree(publication/"overlay",manifest)
def build(*,repo,source_commit,project_root,project_manifest,project_manifest_sha256,git_path,git_sha256,output,runner,before_receipt=None):
 producer=Path(__file__).resolve(); producer_sha=sha256_file(producer); safe(repo,"repo",kind="dir"); safe(project_root,"project root",kind="dir"); require(git_path,git_sha256,"git"); safe(output,"output",absent=True)
 if COMMIT.fullmatch(source_commit) is None: raise OverlayError("source commit malformed")
 git=str(git_path); head=run(runner,"repo_head",[git,"-C",str(repo),"rev-parse","HEAD"],repo).decode().strip(); status=run(runner,"repo_status",[git,"-C",str(repo),"status","--porcelain=v1","--untracked-files=all"],repo)
 if head!=source_commit or status: raise OverlayError("repo commit/status mismatch")
 commit_oids=run(runner,"control_commit_oids",[git,"-C",str(repo),"rev-parse",*[f"{source_commit}:{x}" for x in CONTROL_PATHS]],repo).decode().splitlines(); work_oids=run(runner,"control_worktree_oids",[git,"-C",str(repo),"hash-object","--",*CONTROL_PATHS],repo).decode().splitlines()
 if len(commit_oids)!=3 or commit_oids!=work_oids: raise OverlayError("control Git identity mismatch")
 controls=[]
 for text,oid in zip(CONTROL_PATHS,commit_oids,strict=True):
  path=repo/text; safe(path,text); controls.append({"blob_oid":oid,"bytes":path.stat().st_size,"path":text,"sha256":sha256_file(path)})
 manifest=json.loads((repo/"proofs/lake-manifest.json").read_text())
 if (not isinstance(manifest,dict) or set(manifest)!=MANIFEST_FIELDS or manifest.get("version")!="1.2.0" or manifest.get("name")!="proofs" or manifest.get("packagesDir")!=".lake/packages" or manifest.get("lakeDir")!=".lake" or not isinstance(manifest.get("packages"),list) or any(not isinstance(x,dict) or set(x)!=PACKAGE_FIELDS for x in manifest["packages"])): raise OverlayError("Lake manifest closed schema mismatch")
 packages=[]; roots=[]; names=set(); remotes=set()
 for item in manifest["packages"]:
  name=item.get("name")
  if not isinstance(name,str) or re.fullmatch(r"[A-Za-z][A-Za-z0-9_-]*",name) is None or name in names or item.get("type")!="git" or COMMIT.fullmatch(str(item.get("rev"))) is None or item.get("subDir") is not None: raise OverlayError("Lake package record mismatch")
  names.add(name); facade=repo/"proofs/.lake/packages"/name
  try: package=facade.resolve(strict=True)
  except OSError as error: raise OverlayError(f"cannot resolve package {name}") from error
  safe(package,f"resolved package {name}",kind="dir"); phead=run(runner,f"package_head:{name}",[git,"-C",str(package),"rev-parse","HEAD"],repo).decode().strip(); pstatus=run(runner,f"package_status:{name}",[git,"-C",str(package),"status","--porcelain=v1","--untracked-files=all"],repo); remote=run(runner,f"package_remote:{name}",[git,"-C",str(package),"remote","get-url","origin"],repo).decode().strip(); normalized=normalize_url(remote)
  if phead!=item["rev"] or pstatus or normalized!=normalize_url(item["url"]) or normalized in remotes: raise OverlayError(f"package {name} identity mismatch")
  remotes.add(normalized); root=(package/".lake/build/lib/lean").resolve(strict=True); safe(root,f"package {name} build root",kind="dir"); roots.append((name,package,root)); packages.append({"build_root":str(root),"facade":str(facade),"head":phead,"manifest_url":item["url"],"name":name,"normalized_remote":normalized,"rev":item["rev"]})
 selection=read_selection(project_manifest,project_manifest_sha256); rows=scan(project_root,"project",selection)
 for name,_,root in roots: rows.extend(scan(root,name))
 rows.sort(key=lambda x:x["path"]); paths=[x["path"] for x in rows]
 if len(paths)!=len(set(paths)): raise OverlayError("overlay relative-path collision")
 source_rows=[{k:x[k] for k in ("bytes","origin","path","sha256")} for x in rows]; pins={x["source"]:x["sha256"] for x in rows}; pins.update({str(producer):producer_sha,str(git_path):git_sha256,str(project_manifest):project_manifest_sha256,**{str(repo/x["path"]):x["sha256"] for x in controls}})
 with tempfile.TemporaryDirectory(prefix=".h1-replay-overlay-",dir=output.parent) as raw:
  stage=Path(raw)/"publication"; overlay=stage/"overlay"; overlay.mkdir(parents=True)
  for row in rows:
   destination=overlay/row["path"]; destination.parent.mkdir(parents=True,exist_ok=True); shutil.copyfile(row["source"],destination); require(destination,row["sha256"],"copied entry")
   if destination.stat().st_size!=row["bytes"]: raise OverlayError("copied byte mismatch")
  output_rows=[{k:x[k] for k in ("bytes","path","sha256")} for x in rows]; identity=hashlib.sha256(canonical(output_rows)).hexdigest(); manifest_value={"entry_count":len(rows),"entries":output_rows,"identity_sha256":identity,"included_extensions":list(IMPORT_EXTENSIONS),"schema":SCHEMA}; manifest_raw=canonical(manifest_value); (stage/"manifest.json").write_bytes(manifest_raw)
  if before_receipt: before_receipt()
  for path,pin in pins.items(): require(Path(path),pin,"input drift")
  final=scan(project_root,"project",selection)
  for name,_,root in roots: final.extend(scan(root,name))
  final.sort(key=lambda x:x["path"])
  if [{k:x[k] for k in ("bytes","origin","path","sha256")} for x in final]!=source_rows: raise OverlayError("source census drift")
  if verify_tree(overlay,manifest_value)!=len(rows): raise OverlayError("stage verification failed")
  if run(runner,"repo_head_final",[git,"-C",str(repo),"rev-parse","HEAD"],repo).decode().strip()!=source_commit or run(runner,"repo_status_final",[git,"-C",str(repo),"status","--porcelain=v1","--untracked-files=all"],repo): raise OverlayError("repo drift")
  for package,(name,path,_) in zip(packages,roots,strict=True):
   if Path(package["facade"]).resolve(strict=True)!=path or run(runner,f"package_head_final:{name}",[git,"-C",str(path),"rev-parse","HEAD"],repo).decode().strip()!=package["rev"] or run(runner,f"package_status_final:{name}",[git,"-C",str(path),"status","--porcelain=v1","--untracked-files=all"],repo) or normalize_url(run(runner,f"package_remote_final:{name}",[git,"-C",str(path),"remote","get-url","origin"],repo).decode().strip())!=package["normalized_remote"]: raise OverlayError(f"package {name} drift")
  receipt={"control_files":controls,"entry_count":len(rows),"git_path":str(git_path),"git_sha256":git_sha256,"manifest_path":"manifest.json","manifest_sha256":hashlib.sha256(manifest_raw).hexdigest(),"overlay_identity_sha256":identity,"packages":packages,"producer_path":str(producer),"producer_sha256":producer_sha,"project_manifest_path":str(project_manifest),"project_manifest_sha256":project_manifest_sha256,"project_root":str(project_root),"repo":str(repo),"schema":RECEIPT_SCHEMA,"source_commit":source_commit}; (stage/"receipt.json").write_bytes(canonical(receipt)); fsync_tree(stage)
  if output.exists() or output.is_symlink(): raise OverlayError("output appeared")
  stage.rename(output); fd=os.open(output.parent,os.O_RDONLY)
  try: os.fsync(fd)
  finally: os.close(fd)
def main():
 parser=argparse.ArgumentParser(description=__doc__); parser.add_argument("--repo",type=Path); parser.add_argument("--source-commit"); parser.add_argument("--project-root",type=Path); parser.add_argument("--project-manifest",type=Path); parser.add_argument("--project-manifest-sha256"); parser.add_argument("--git-path",type=Path); parser.add_argument("--git-sha256"); parser.add_argument("--output",type=Path); parser.add_argument("--verify",type=Path); args=parser.parse_args()
 try:
  if args.verify is not None:
   if any(x is not None for x in (args.repo,args.source_commit,args.project_root,args.project_manifest,args.project_manifest_sha256,args.git_path,args.git_sha256,args.output)): raise OverlayError("verify/build arguments mixed")
   print(f"VERIFIED files={verify(args.verify)}")
  else:
   required=(args.repo,args.source_commit,args.project_root,args.project_manifest,args.project_manifest_sha256,args.git_path,args.git_sha256,args.output)
   if any(x is None for x in required): raise OverlayError("build inputs incomplete")
   def runner(kind,argv,cwd):
    result=subprocess.run(argv,cwd=cwd,stdout=subprocess.PIPE,stderr=subprocess.PIPE); return {"rc":result.returncode,"stdout":result.stdout,"stderr":result.stderr}
   build(repo=args.repo,source_commit=args.source_commit,project_root=args.project_root,project_manifest=args.project_manifest,project_manifest_sha256=args.project_manifest_sha256,git_path=args.git_path,git_sha256=args.git_sha256,output=args.output,runner=runner); print(f"WROTE files={verify(args.output)}")
  return 0
 except (OSError,OverlayError) as error: print(f"OVERLAY_ERROR: {error}"); return 2
if __name__=="__main__": raise SystemExit(main())
