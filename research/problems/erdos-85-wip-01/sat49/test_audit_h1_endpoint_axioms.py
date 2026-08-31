#!/usr/bin/env python3
import hashlib,importlib.util,json,tempfile,unittest
from pathlib import Path
from unittest import mock

HERE=Path(__file__).resolve().parent
def load(name,path):
 spec=importlib.util.spec_from_file_location(name,path); module=importlib.util.module_from_spec(spec)
 assert spec.loader is not None; spec.loader.exec_module(module); return module
MOD=load("h1_axiom_wrapper",HERE/"audit_h1_endpoint_axioms.py")
COLD=load("h1_cold",HERE/"run_h1_endpoint_cold_build.py")
COLD_TEST=load("h1_cold_test",HERE/"test_run_h1_endpoint_cold_build.py")

def pretty(path,value): path.parent.mkdir(parents=True,exist_ok=True); path.write_text(json.dumps(value,indent=2)+"\n")

def fixture(root):
 root=root.resolve(); cold_args,_,_=COLD_TEST.fixture(root); cold_args["output"]=root/"cold"
 COLD.build(**cold_args); cold_receipt=cold_args["output"]/"receipt.json"
 cold_value=json.loads(cold_receipt.read_text()); commit=cold_value["source_commit"]
 h1_artifact=cold_args["output"]/"artifacts/generated/Proofs/Generated/H1.olean"
 h1_artifact.parent.mkdir(parents=True,exist_ok=True); h1_artifact.write_bytes(b"h1 olean\n")
 cold_value["retained_generated_artifacts"].append({"artifact_path":"artifacts/generated/Proofs/Generated/H1.olean",
  "build_path":".lake/build/lib/lean/Proofs/Generated/H1.olean","bytes":h1_artifact.stat().st_size,
  "sha256":MOD.sha(h1_artifact)})
 cold_value["retained_generated_artifacts"].sort(key=lambda row:row["build_path"])
 cold_receipt.write_bytes(MOD.canonical(cold_value))
 lake_package={"configFile":None,"inherited":False,"inputRev":None,"manifestFile":None,"name":"mathlib",
  "rev":"f"*40,"scope":"","subDir":None,"type":"git","url":"https://github.com/leanprover-community/mathlib4"}
 batteries_package={**lake_package,"name":"batteries","rev":"6"*40,"url":"git@github.com:leanprover-community/batteries.git"}
 lake_manifest={"fixedToolchain":None,"lakeDir":".lake","name":"proofs","packages":[lake_package,batteries_package],
                "packagesDir":".lake/packages","version":"1.2.0"}
 state={"audit_rc":0,"bad_tools":False,"foreign":False,"sorry":False,"generated_drift":False,
        "bad_source_oids":False,"dirty_after":False,"forbidden":False,"unattributed":False,
        "extra_audit":False,"bad_python":False,"inherited_lake":False,"foreign_lake":False,
        "swap_roots":False,"swapped_tools":False,"disconnected_generated":False}
 source_raw=b"import Proofs.Generated.H1\n\ntheorem endpoint : True := by trivial\n"
 def checkout_from(argv):
  mounts=[x for x in argv if x.endswith(":/workspace:rw")]
  return Path(mounts[0].split(":/workspace:rw")[0]) if mounts else Path(argv[argv.index("-C")+1])
 def runner(kind,argv,cwd,environment,stdout,stderr):
  stdout.write_bytes(b""); stderr.write_bytes(b"")
  if kind=="clone":
   checkout=Path(argv[-1]); checkout.mkdir(); (checkout/".git").mkdir()
  else: checkout=checkout_from(argv)
  if kind=="checkout":
   for identity in cold_value["reviewed_control_files"]:
    path=checkout/identity["path"]; path.parent.mkdir(parents=True,exist_ok=True)
    path.write_bytes(MOD.canonical(lake_manifest) if identity["path"].endswith("lake-manifest.json") else (identity["path"]+"\n").encode())
   endpoint=checkout/MOD.SOURCE; endpoint.parent.mkdir(parents=True,exist_ok=True)
   endpoint.write_bytes(source_raw)
   sources={"proofs/Proofs/Generated/Leaf.lean":"import Proofs.Support\ntheorem Erdos85.endpointRoot : True := by trivial\n",
    "proofs/Proofs/Generated/Aggregate.lean":"import Proofs.Generated.Leaf\ntheorem Erdos85.aggregate : True := by trivial\n",
    "proofs/Proofs/Generated/H1.lean":("import Proofs.Support\n" if state["disconnected_generated"] else "import Proofs.Generated.Aggregate\n")+"theorem Erdos85.h1 : True := by trivial\n",
    "proofs/Proofs/Support.lean":"theorem Erdos85.support : True := by trivial\n"}
   for text,raw in sources.items(): path=checkout/text; path.parent.mkdir(parents=True,exist_ok=True); path.write_text(raw)
   if state["inherited_lake"]:
    inherited=checkout/"proofs/.lake/inherited"; inherited.parent.mkdir(parents=True); inherited.write_text("bad\n")
   for text in (MOD.AUDITOR,MOD.HELPER,MOD.COLD_PRODUCER,MOD.SNAPSHOT_PRODUCER):
    source=(HERE.parents[4]/text) if False else None
    actual={MOD.AUDITOR:HERE.parents[3]/MOD.AUDITOR,MOD.HELPER:HERE.parents[3]/MOD.HELPER,
            MOD.COLD_PRODUCER:HERE/MOD.COLD_PRODUCER.split("/")[-1],
            MOD.SNAPSHOT_PRODUCER:HERE/MOD.SNAPSHOT_PRODUCER.split("/")[-1]}[text]
    path=checkout/text; path.parent.mkdir(parents=True,exist_ok=True); path.write_bytes(actual.read_bytes())
   if state["sorry"]: (checkout/"proofs/Proofs/Generated/Leaf.lean").write_text("theorem bad : True := by sorry\n")
  elif kind=="head": stdout.write_text(commit+"\n")
  elif kind in ("status","status_after"): stdout.write_text(" M bad\n" if kind=="status_after" and state["dirty_after"] else "")
  elif kind in ("audit_source_commit_oids","audit_source_worktree_oids","project_commit_oids","project_worktree_oids"):
   count=len(argv)-(argv.index("rev-parse")+1) if "rev-parse" in argv else len(argv)-(argv.index("--")+1)
   values=[f"{index+1:040x}" for index in range(count)]
   if kind.startswith("audit_source_"): values[-1]=cold_value["cache_snapshot_producer_identity"]["blob_oid"]
   if state["bad_source_oids"] and kind.endswith("worktree_oids"): values[0]="f"*40
   stdout.write_text("\n".join(values)+"\n")
  elif kind=="tool_hashes": stdout.write_text("bad\n" if state["bad_tools"] else
    ("1"*64+"  /root/.elan/bin/lean\n"+"0"*64+"  /usr/bin/python3\n" if state["swapped_tools"] else
     "0"*64+"  /usr/bin/python3\n"+"1"*64+"  /root/.elan/bin/lean\n")+"2"*64+"  /root/.elan/bin/lake\n")
  elif kind=="python_version": stdout.write_text("spoof\n" if state["bad_python"] else "Python 3.13.0\n")
  elif kind=="lean_version": stdout.write_text("Lean (version 4.31.0, fake)\n")
  elif kind=="lake_version": stdout.write_text("Lake version 5.0.0-fake\n")
  elif kind=="audit":
   audit_output=checkout/".h1-axiom-output"; audit_output.mkdir()
   native="Erdos85.endpointRoot._native.native_decide.ax_1"; native2="Erdos85.endpointOther._native.native_decide.ax_2"
   theorems=[{"name":"Erdos85.endpointOther","module":"Proofs.Generated.Leaf","direct_axioms":[native2],
     "transitive_axioms":["Classical.choice",native2]},
    {"name":"Erdos85.endpointRoot","module":"Proofs.Foreign" if state["foreign"] else "Proofs.Generated.Leaf",
     "direct_axioms":[native],"transitive_axioms":["Classical.choice",native]},
    {"name":MOD.THEOREM,"module":MOD.MODULE,"direct_axioms":[],
     "transitive_axioms":sorted(["Classical.choice","Quot.sound",native,native2,"propext"])}]
   if state["forbidden"]: theorems[-1]["transitive_axioms"]=sorted(theorems[-1]["transitive_axioms"]+["Lean.ofReduceBool"])
   roots=[] if state["unattributed"] else [
    {"theorem":"Erdos85.endpointOther","module":"Proofs.Generated.Leaf","axiom":native if state["swap_roots"] else native2,"family":"h1-committed"},
    {"theorem":"Erdos85.endpointRoot","module":"Proofs.Generated.Leaf","axiom":native2 if state["swap_roots"] else native,"family":"h1-committed"}]
   allow_path=checkout/"proofs/.h1-axiom-allowlist.json"
   inventory={"schema":1,"generated_at":"2026-08-31T00:00:00+00:00","git_commit":commit,"module":MOD.MODULE,"target":MOD.THEOREM,
    "allowlist_path":"proofs/.h1-axiom-allowlist.json","allowlist_sha256":MOD.sha(allow_path),
    "theorem_count":3,"native_roots":roots,"theorems":theorems}
   pretty(audit_output/"dependency-cone.json",inventory)
   discovery=b"ERDOS85_CONE fixture\n"; (audit_output/"dependency-cone.log").write_bytes(discovery)
   delimiters=b"".join((f"ERDOS85_AXIOM_BEGIN\t{x['name']}\nERDOS85_AXIOM_END\t{x['name']}\n").encode() for x in theorems)
   (audit_output/"print-axioms.log").write_bytes(delimiters)
   artifacts={"dependency_cone":"dependency-cone.json","dependency_cone_sha256":MOD.sha(audit_output/"dependency-cone.json"),
    "discovery_log":"dependency-cone.log","discovery_log_sha256":hashlib.sha256(discovery).hexdigest(),
    "print_axioms_log":"print-axioms.log","print_axioms_log_sha256":hashlib.sha256(delimiters).hexdigest()}
   receipt={"schema":1,"status":"PASS","target":MOD.THEOREM,"theorem_count":3,"literal_theorem_count":3,
    "private_environment_theorem_count":0,"private_environment_theorems":[],"native_root_count":len(roots),
    "native_family_counts":{"h1-committed":len(roots)},"errors":[],"artifacts":artifacts}
   pretty(audit_output/"audit-receipt.json",receipt); stdout.write_text(json.dumps(receipt,indent=2)+"\n")
   if state["extra_audit"]: (audit_output/"extra").write_text("extra\n")
   if state["generated_drift"]:
    generated=checkout/"proofs/.lake/build/lib/lean/Proofs/Generated"; (generated/"Late.olean").write_bytes(b"late\n")
   if state["foreign_lake"]:
    foreign_lake=checkout/"proofs/.lake/build/lib/lean/Proofs/Foreign.olean"; foreign_lake.parent.mkdir(parents=True,exist_ok=True); foreign_lake.write_bytes(b"late\n")
   helper=checkout/"proofs/.lake/build/lib/lean/Proofs/Erdos85DependencyConeAudit.olean"
   helper.parent.mkdir(parents=True,exist_ok=True); helper.write_bytes(b"helper olean\n")
   helper.with_suffix(".ilean").write_bytes(b"helper ilean\n")
  return {"cumulative_children_maxrss_kb":1,"rc":state["audit_rc"] if kind=="audit" else 0,
          "system_ns":1,"user_ns":1,"wall_ns":1}
 args={"repo":cold_args["repo"],"cold_receipt":cold_receipt,"cold_pin":MOD.sha(cold_receipt),
       "output":root/"audit-bank","runner":runner}
 return args,state,{"cold":cold_receipt}

class AuditH1EndpointAxiomsTest(unittest.TestCase):
 def test_happy_path_is_exact_networkless_and_atomic(self):
  with tempfile.TemporaryDirectory() as directory:
   root=Path(directory); args,_,_=fixture(root); receipt=MOD.build(**args); out=args["output"]
   self.assertEqual(receipt["schema"],MOD.SCHEMA); self.assertEqual(receipt["native_root_count"],2)
   self.assertIn("--network=none",receipt["commands"]["audit"]["argv"])
   self.assertNotIn("--inventory-only",receipt["commands"]["audit"]["argv"])
   self.assertEqual(receipt["tool_identities"]["lean_sha256"],"1"*64)
   self.assertTrue(all(MOD.sha(out/row["path"])==row["sha256"] for row in receipt["artifacts"]))
   with self.assertRaisesRegex(ValueError,"output.*absent"): MOD.build(**args)
 def test_audit_and_source_adversaries_fail(self):
  cases=(("foreign","foreign","theorem inventory"),("sorry","sorry","sorry/admit"),
         ("generated","generated_drift","changed restored Generated"),("oid","bad_source_oids","Git identity"),
         ("tool","bad_tools","tool identity"),("dirty","dirty_after","changed committed source"),
         ("rc","audit_rc","audit command"),("forbidden","forbidden","forbidden/foreign"),
         ("unattributed","unattributed","native root attribution"),("extra-audit","extra_audit","artifact file set"),
         ("python","bad_python","Python version"),("inherited-lake","inherited_lake","inherited .lake"),
         ("foreign-lake","foreign_lake","restored .lake"),("swapped-root","swap_roots","native root attribution"),
         ("swapped-tools","swapped_tools","tool identity"),
         ("disconnected-generated","disconnected_generated","endpoint import closure"))
  for name,key,message in cases:
   with self.subTest(name=name),tempfile.TemporaryDirectory() as directory:
    root=Path(directory); args,state,_=fixture(root); state[key]=2 if key=="audit_rc" else True
    with self.assertRaisesRegex(ValueError,message): MOD.build(**args)
    self.assertFalse(args["output"].exists())
 def test_input_and_output_toctou_fail(self):
  with tempfile.TemporaryDirectory() as directory:
   root=Path(directory); args,_,paths=fixture(root); original=paths["cold"].read_bytes()
   args["before_receipt"]=lambda:paths["cold"].write_bytes(original+b"x")
   with self.assertRaisesRegex(ValueError,"input drift"): MOD.build(**args)
   self.assertFalse(args["output"].exists())
  with tempfile.TemporaryDirectory() as directory:
   root=Path(directory); args,_,_=fixture(root)
   def mutate_retained():
    matches=list(root.glob(".h1-axiom-audit-*/publication/audit/dependency-cone.json")); assert len(matches)==1
    matches[0].write_bytes(matches[0].read_bytes()+b"x")
   args["before_receipt"]=mutate_retained
   with self.assertRaisesRegex(ValueError,"retained audit artifact"): MOD.build(**args)
  callbacks=(
   ("publication-extra",lambda root:(root.glob(".h1-axiom-audit-*/publication")),"file"),
   ("publication-special",lambda root:(root.glob(".h1-axiom-audit-*/publication")),"fifo"),
   ("lake-extra",lambda root:(root.glob(".h1-axiom-audit-*/checkout/proofs/.lake")),"file"),
   ("helper-mutation",lambda root:(root.glob(".h1-axiom-audit-*/checkout/proofs/.lake/build/lib/lean/Proofs")),"helper"))
  for name,finder,kind in callbacks:
   with self.subTest(name=name),tempfile.TemporaryDirectory() as directory:
    root=Path(directory); args,_,_=fixture(root)
    def mutate(root=root,finder=finder,kind=kind):
     matches=list(finder(root)); assert len(matches)==1
     target=matches[0]/("late.fifo" if kind=="fifo" else
                       "Erdos85DependencyConeAudit.olean" if kind=="helper" else "late.bin")
     if kind=="fifo": MOD.os.mkfifo(target)
     else: target.write_bytes(b"late\n")
    args["before_receipt"]=mutate
    with self.assertRaisesRegex(ValueError,r"publication|\.lake|scanned tree file"): MOD.build(**args)
    self.assertFalse(args["output"].exists())
  with tempfile.TemporaryDirectory() as directory:
   root=Path(directory); args,_,_=fixture(root); cold=json.loads(args["cold_receipt"].read_text())
   cold_log=args["cold_receipt"].parent/cold["commands"]["build"]["stdout_path"]
   args["before_receipt"]=lambda:cold_log.write_bytes(cold_log.read_bytes()+b"late\n")
   with self.assertRaisesRegex(ValueError,"input drift"): MOD.build(**args)
 def test_cold_contract_spoofs_fail(self):
  def forge_argv(cold):
   record=cold["commands"]["build"]; record["argv"].append("spoof")
   core={"argv":record["argv"],"cwd":record["cwd"],"environment":record["environment"],"kind":"build"}
   record["command_identity_sha256"]=hashlib.sha256(MOD.canonical(core)).hexdigest()
  def relative_stage(cold):
   old_stage=cold["commands"]["clone"]["cwd"]; old_checkout=cold["commands"]["clone"]["argv"][-1]
   for kind,record in cold["commands"].items():
    record["cwd"]="relative-stage"
    record["argv"]=[token.replace(old_checkout,"relative-stage/checkout").replace(old_stage,"relative-stage") for token in record["argv"]]
    core={"argv":record["argv"],"cwd":record["cwd"],"environment":record["environment"],"kind":kind}
    record["command_identity_sha256"]=hashlib.sha256(MOD.canonical(core)).hexdigest()
  mutations=(
   ("policy",lambda cold:cold["resource_policy"].update({"cpus":7}),"resource policy"),
   ("argv",forge_argv,"command evidence identity"),
   ("snapshot-bytes",lambda cold:cold["cache_snapshot_producer_identity"].update({"bytes":1}),"snapshot producer path/bytes"),
   ("zero-rss",lambda cold:cold["commands"]["build"].update({"cumulative_children_maxrss_kb":0}),"command evidence identity"),
   ("relative-stage",relative_stage,"stage/checkout path identity"))
  for name,mutate,message in mutations:
   with self.subTest(name=name),tempfile.TemporaryDirectory() as directory:
    root=Path(directory); args,_,_=fixture(root); cold=json.loads(args["cold_receipt"].read_text())
    mutate(cold); args["cold_receipt"].write_bytes(MOD.canonical(cold)); args["cold_pin"]=MOD.sha(args["cold_receipt"])
    with self.assertRaisesRegex(ValueError,message): MOD.build(**args)
    self.assertFalse(args["output"].exists())
 def test_restoration_copy_and_symlink_fail(self):
  with tempfile.TemporaryDirectory() as directory:
   root=Path(directory); args,_,_=fixture(root); real_copy=MOD.shutil.copyfile
   def corrupt(source,destination):
    result=real_copy(source,destination)
    if str(destination).endswith("Proofs/Generated/Leaf.olean"): Path(destination).write_bytes(b"corrupt\n")
    return result
   with mock.patch.object(MOD.shutil,"copyfile",side_effect=corrupt):
    with self.assertRaisesRegex(ValueError,"restored generated artifact"): MOD.build(**args)
  with tempfile.TemporaryDirectory() as directory:
   root=Path(directory); args,_,_=fixture(root); cold=json.loads(args["cold_receipt"].read_text())
   row=next(item for item in cold["retained_generated_artifacts"] if item["build_path"].endswith("Leaf.olean"))
   artifact=args["cold_receipt"].parent/row["artifact_path"]; real=artifact.with_suffix(".real")
   artifact.rename(real); artifact.symlink_to(real)
   with self.assertRaisesRegex(ValueError,"retained generated artifact"): MOD.build(**args)
  for name,suffix,message in (("helper","audit/helper/Erdos85DependencyConeAudit.olean","retained audit helper"),
                              ("allowlist","audit/allowlist.json","retained allowlist")):
   with self.subTest(name=name),tempfile.TemporaryDirectory() as directory:
    root=Path(directory); args,_,_=fixture(root); real_copy=MOD.shutil.copyfile
    def corrupt_retained(source,destination,suffix=suffix):
     result=real_copy(source,destination)
     if str(destination).endswith(suffix): Path(destination).write_bytes(b"corrupt\n")
     return result
    with mock.patch.object(MOD.shutil,"copyfile",side_effect=corrupt_retained):
     with self.assertRaisesRegex(ValueError,message): MOD.build(**args)

if __name__=="__main__": unittest.main()
