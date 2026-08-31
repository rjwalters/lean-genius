import json, os, sys, tempfile, unittest
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent))
import build_replay_overlay as target

COMMIT="a"*40; REV="b"*40; OID="c"*40
class OverlayTests(unittest.TestCase):
 def fixture(self,base):
  repo=base/"repo"; proofs=repo/"proofs"; package=proofs/".lake/packages/dep"; root=package/".lake/build/lib/lean"; project=base/"project"
  root.mkdir(parents=True); project.mkdir(); (root/"Dep.olean").write_bytes(b"dep"); (project/"Project.olean").write_bytes(b"project")
  (proofs/"lean-toolchain").write_text("leanprover/lean4:v4.31.0\n"); (proofs/"lakefile.toml").write_text('name="proofs"\n')
  record={key:None for key in target.PACKAGE_FIELDS}; record.update({"name":"dep","type":"git","rev":REV,"subDir":None,"url":"https://github.com/example/dep"})
  manifest={key:None for key in target.MANIFEST_FIELDS}; manifest.update({"fixedToolchain":False,"lakeDir":".lake","name":"proofs","packages":[record],"packagesDir":".lake/packages","version":"1.2.0"})
  (proofs/"lake-manifest.json").write_text(json.dumps(manifest)); selection=base/"project.tsv"; selection.write_text(f"{target.sha256_file(project/'Project.olean')}\tProject.olean\n")
  git=base/"git"; git.write_bytes(b"git"); git.chmod(0o755)
  def runner(kind,argv,cwd):
   if kind in ("control_commit_oids","control_worktree_oids"): out=((OID+"\n")*3).encode()
   elif "status" in kind: out=b""
   elif kind.startswith("package_head"): out=(REV+"\n").encode()
   elif kind.startswith("package_remote"): out=b"https://github.com/example/dep.git\n"
   else: out=(COMMIT+"\n").encode()
   return {"rc":0,"stdout":out,"stderr":b""}
  return repo,project,selection,git,runner
 def build(self,base,before=None):
  repo,project,selection,git,runner=self.fixture(base); output=base/"output"
  target.build(repo=repo,source_commit=COMMIT,project_root=project,project_manifest=selection,project_manifest_sha256=target.sha256_file(selection),git_path=git,git_sha256=target.sha256_file(git),output=output,runner=runner,before_receipt=before)
  return output,project
 def test_authenticated_atomic_build_and_verify(self):
  with tempfile.TemporaryDirectory() as raw:
   output,_=self.build(Path(raw).resolve()); self.assertEqual(target.verify(output),2)
   receipt=json.loads((output/"receipt.json").read_text()); self.assertEqual(receipt["packages"][0]["rev"],REV); self.assertEqual(receipt["schema"],target.RECEIPT_SCHEMA)
 def test_tamper_missing_extra_and_hardlink_rejected(self):
  for mutation in ("tamper","missing","extra"):
   with self.subTest(mutation=mutation),tempfile.TemporaryDirectory() as raw:
    output,_=self.build(Path(raw).resolve()); leaf=output/"overlay/Dep.olean"
    if mutation=="tamper": leaf.write_bytes(b"evil")
    elif mutation=="missing": leaf.unlink()
    else: (output/"overlay/Extra.olean").write_bytes(b"evil")
    with self.assertRaises(target.OverlayError): target.verify(output)
  with tempfile.TemporaryDirectory() as raw:
   base=Path(raw).resolve(); root=base/"root"; root.mkdir(); a=root/"A.olean"; a.write_bytes(b"x"); os.link(a,root/"B.olean")
   with self.assertRaisesRegex(target.OverlayError,"hardlink"): target.scan(root,"dep")
 def test_collision_rejected(self):
  with tempfile.TemporaryDirectory() as raw:
   base=Path(raw).resolve(); a=base/"a"; b=base/"b"; a.mkdir(); b.mkdir(); (a/"Same.olean").write_bytes(b"a"); (b/"Same.olean").write_bytes(b"b")
   rows=target.scan(a,"a")+target.scan(b,"b"); paths=[row["path"] for row in rows]; self.assertNotEqual(len(paths),len(set(paths)))
 def test_source_drift_rolls_back_publication(self):
  with tempfile.TemporaryDirectory() as raw:
   base=Path(raw).resolve(); holder={}
   repo,project,selection,git,runner=self.fixture(base); output=base/"output"
   def mutate(): (project/"Project.olean").write_bytes(b"changed")
   with self.assertRaisesRegex(target.OverlayError,"input drift"):
    target.build(repo=repo,source_commit=COMMIT,project_root=project,project_manifest=selection,project_manifest_sha256=target.sha256_file(selection),git_path=git,git_sha256=target.sha256_file(git),output=output,runner=runner,before_receipt=mutate)
   self.assertFalse(output.exists())
 def test_closed_manifest_and_package_identity_rejected(self):
  with tempfile.TemporaryDirectory() as raw:
   base=Path(raw).resolve(); repo,project,selection,git,runner=self.fixture(base); lake=repo/"proofs/lake-manifest.json"; value=json.loads(lake.read_text()); value["extra"]=True; lake.write_text(json.dumps(value))
   with self.assertRaisesRegex(target.OverlayError,"closed schema"):
    target.build(repo=repo,source_commit=COMMIT,project_root=project,project_manifest=selection,project_manifest_sha256=target.sha256_file(selection),git_path=git,git_sha256=target.sha256_file(git),output=base/"output",runner=runner)
  with tempfile.TemporaryDirectory() as raw:
   base=Path(raw).resolve(); repo,project,selection,git,runner=self.fixture(base); lake=repo/"proofs/lake-manifest.json"; value=json.loads(lake.read_text()); value["packages"][0]["rev"]="d"*40; lake.write_text(json.dumps(value))
   with self.assertRaisesRegex(target.OverlayError,"package dep identity"):
    target.build(repo=repo,source_commit=COMMIT,project_root=project,project_manifest=selection,project_manifest_sha256=target.sha256_file(selection),git_path=git,git_sha256=target.sha256_file(git),output=base/"output",runner=runner)
if __name__=="__main__": unittest.main()
