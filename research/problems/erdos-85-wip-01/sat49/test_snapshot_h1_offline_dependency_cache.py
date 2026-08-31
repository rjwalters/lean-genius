#!/usr/bin/env python3
import hashlib,importlib.util,json,os,tempfile,unittest
from pathlib import Path
from unittest import mock
HERE=Path(__file__).resolve().parent; spec=importlib.util.spec_from_file_location("cache",HERE/"snapshot_h1_offline_dependency_cache.py")
MOD=importlib.util.module_from_spec(spec); assert spec.loader is not None; spec.loader.exec_module(MOD)
def h(data): return hashlib.sha256(data).hexdigest()
def fixture(root):
 root=root.resolve(); repo=root/"repo"; proofs=repo/"proofs"; cache=proofs/".lake"; cache.mkdir(parents=True)
 commit="a"*40; packages=[("mathlib","b"*40,"https://github.com/leanprover-community/mathlib4"),
  ("aesop","c"*40,"https://github.com/leanprover-community/aesop")]
 manifest={"version":"1.2.0","packagesDir":".lake/packages","packages":[],"name":"proofs","lakeDir":".lake","fixedToolchain":False}
 for name,rev,url in packages:
  manifest["packages"].append({"url":url,"type":"git","subDir":None,"scope":"leanprover-community","rev":rev,
   "name":name,"manifestFile":"lake-manifest.json","inputRev":"main","inherited":name!="mathlib","configFile":"lakefile.toml"})
  package=cache/"packages"/name; (package/".git").mkdir(parents=True); (package/"Source.lean").write_text(f"-- {name}\n")
 controls={"proofs/lean-toolchain":b"leanprover/lean4:v4.31.0\n","proofs/lakefile.toml":b"name='proofs'\n",
           "proofs/lake-manifest.json":json.dumps(manifest).encode()+b"\n"}
 for text,data in controls.items(): path=repo/text; path.parent.mkdir(parents=True,exist_ok=True); path.write_bytes(data)
 (cache/"build/lib/lean/Mathlib.olean").parent.mkdir(parents=True); (cache/"build/lib/lean/Mathlib.olean").write_bytes(b"mathlib olean")
 state={"repo_head":commit,"repo_dirty":False,"package_head":{},"package_dirty":set(),"remote":{},"bad_control":False}
 git=root/"git"; git.write_text("fake git\n")
 for name,rev,url in packages: state["package_head"][name]=rev; state["remote"][name]=url+".git"
 def runner(kind,argv,cwd):
  stderr=b""; stdout=b""
  if kind in ("repo_head","repo_head_final"): stdout=(state["repo_head"]+"\n").encode()
  elif kind in ("repo_status","repo_status_final"): stdout=b" M dirty\n" if state["repo_dirty"] else b""
  elif kind in ("control_commit_oids","control_worktree_oids"):
   values=[hashlib.sha1(b"blob "+str(len(controls[p])).encode()+b"\0"+controls[p]).hexdigest() for p in MOD.CONTROL_PATHS]
   if state["bad_control"] and kind=="control_worktree_oids": values[0]="f"*40
   stdout=("\n".join(values)+"\n").encode()
  elif kind.startswith("package_head:") or kind.startswith("package_head_final:"):
   name=kind.split(":",1)[1]; stdout=(state["package_head"][name]+"\n").encode()
  elif kind.startswith("package_status:") or kind.startswith("package_status_final:"):
   name=kind.split(":",1)[1]; stdout=b"?? bad\n" if name in state["package_dirty"] else b""
  elif kind.startswith("package_remote:") or kind.startswith("package_remote_final:"):
   name=kind.split(":",1)[1]; stdout=(state["remote"][name]+"\n").encode()
  return {"rc":0,"stdout":stdout,"stderr":stderr}
 return [repo,commit,cache,git,MOD.sha(git),root/"out",runner],state,{"repo":repo,"cache":cache,"manifest":proofs/"lake-manifest.json"}

class CacheSnapshotTest(unittest.TestCase):
 def test_happy_snapshot_is_exact_and_atomic(self):
  with tempfile.TemporaryDirectory() as directory:
   root=Path(directory); args,state,paths=fixture(root); MOD.build(*args); out=root/"out"
   receipt=json.loads((out/"receipt.json").read_text()); manifest=json.loads((out/"cache-manifest.json").read_text())
   self.assertEqual(receipt["schema"],MOD.RECEIPT_SCHEMA); self.assertEqual(receipt["package_count"],2)
   self.assertEqual(manifest["schema"],MOD.SCHEMA); self.assertEqual(manifest["root"],str((out/"cache").resolve()))
   self.assertEqual(manifest["identity_sha256"],h(MOD.canonical(manifest["entries"])))
   self.assertEqual([x["path"] for x in manifest["entries"]],sorted(x["path"] for x in manifest["entries"]))
   for item in manifest["entries"]: self.assertEqual(MOD.sha(out/"cache"/item["path"]),item["sha256"])
   with self.assertRaisesRegex(ValueError,"output.*absent"): MOD.build(*args)
 def test_git_manifest_and_generated_adversaries(self):
  cases=(("repo-head",lambda a,s,p:s.__setitem__("repo_head","f"*40),"repo commit/status"),
   ("repo-dirty",lambda a,s,p:s.__setitem__("repo_dirty",True),"repo commit/status"),
   ("package-head",lambda a,s,p:s["package_head"].__setitem__("mathlib","f"*40),"revision/status/remote"),
   ("package-dirty",lambda a,s,p:s["package_dirty"].add("aesop"),"revision/status/remote"),
   ("remote",lambda a,s,p:s["remote"].__setitem__("mathlib","https://evil.invalid/x"),"remote"),
   ("control",lambda a,s,p:s.__setitem__("bad_control",True),"control Git identity"),
   ("generated",add_generated,"Generated Lean artifact"),
   ("manifest",mutate_manifest,"closed schema"))
  for name,mutate,message in cases:
   with self.subTest(name=name),tempfile.TemporaryDirectory() as directory:
    root=Path(directory); args,state,paths=fixture(root); mutate(args,state,paths)
    with self.assertRaisesRegex(ValueError,message): MOD.build(*args)
 def test_symlink_copy_toctou_and_retry(self):
  with tempfile.TemporaryDirectory() as directory:
   root=Path(directory); args,state,paths=fixture(root); target=paths["cache"]/"packages/mathlib/Source.lean"
   real=target.with_suffix(".real"); target.rename(real); target.symlink_to(real)
   with self.assertRaisesRegex(ValueError,"symlink"): MOD.build(*args)
  with tempfile.TemporaryDirectory() as directory:
   root=Path(directory); args,state,paths=fixture(root); original=paths["manifest"].read_bytes()
   args.append(lambda:paths["manifest"].write_bytes(original+b"x"))
   with self.assertRaisesRegex(ValueError,"input drift"): MOD.build(*args)
   self.assertFalse((root/"out").exists()); paths["manifest"].write_bytes(original); args.pop(); MOD.build(*args)
  with tempfile.TemporaryDirectory() as directory:
   root=Path(directory); args,state,paths=fixture(root); real_copy=MOD.shutil.copyfile
   def corrupt(source,destination):
    result=real_copy(source,destination)
    if str(destination).endswith("Source.lean"): Path(destination).write_bytes(b"bad")
    return result
   with mock.patch.object(MOD.shutil,"copyfile",side_effect=corrupt):
    with self.assertRaisesRegex(ValueError,"copied cache entry"): MOD.build(*args)
  with tempfile.TemporaryDirectory() as directory:
   root=Path(directory); args,state,paths=fixture(root); source=paths["cache"]/"packages/mathlib/Source.lean"
   alias=paths["cache"]/"packages/mathlib/Alias.lean"; os.link(source,alias)
   with self.assertRaisesRegex(ValueError,"hardlink/alias"): MOD.build(*args)
  for name,callback,message in (
   ("source-add",lambda root,args,state,paths:lambda:(paths["cache"]/"late").write_text("late\n"),"source cache file set"),
   ("source-delete",lambda root,args,state,paths:lambda:(paths["cache"]/"build/lib/lean/Mathlib.olean").unlink(),"input drift"),
   ("snapshot-add",lambda root,args,state,paths:lambda:add_snapshot_file(root),"snapshot cache file set"),
   ("final-head",lambda root,args,state,paths:lambda:state["package_head"].__setitem__("mathlib","f"*40),"package drift"),
   ("final-dirty",lambda root,args,state,paths:lambda:state["package_dirty"].add("mathlib"),"package drift"),
   ("final-remote",lambda root,args,state,paths:lambda:state["remote"].__setitem__("mathlib","git@github.com:evil/repo.git"),"package drift")):
   with self.subTest(late=name),tempfile.TemporaryDirectory() as directory:
    root=Path(directory); args,state,paths=fixture(root); args.append(callback(root,args,state,paths))
    with self.assertRaisesRegex(ValueError,message): MOD.build(*args)

def add_generated(args,state,paths):
 path=paths["cache"]/"build/lib/lean/Proofs/Generated/Leaf.olean"; path.parent.mkdir(parents=True); path.write_bytes(b"bad")
def mutate_manifest(args,state,paths):
 value=json.loads(paths["manifest"].read_text()); value["extra"]=True; paths["manifest"].write_text(json.dumps(value)+"\n")
def add_snapshot_file(root):
 matches=list(root.resolve().glob(".h1-cache-snapshot-*/publication/cache/.lake")); assert len(matches)==1
 (matches[0]/"late").write_text("late\n")
if __name__=="__main__": unittest.main()
