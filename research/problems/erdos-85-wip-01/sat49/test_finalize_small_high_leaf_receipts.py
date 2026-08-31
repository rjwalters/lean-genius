import importlib.util,json,subprocess,tempfile,unittest
from pathlib import Path

HERE=Path(__file__).resolve().parent
def load(name,file):
 spec=importlib.util.spec_from_file_location(name,HERE/file); mod=importlib.util.module_from_spec(spec); assert spec.loader; spec.loader.exec_module(mod); return mod
MOD=load("finalizer","finalize_small_high_leaf_receipts.py")
SOCKET=load("socket","build_small_high_socket_artifacts.py")

def fixture(root):
 bank=root/"bank"; bank.mkdir(); jobs=MOD.ordered_jobs(); payload_rows=[]; audits=[]
 for job in jobs:
  payload=bank/f"{job}.lrat"; payload.write_text("0\n"); psha=MOD.sha(payload)
  evidence={"accepted":True,"accepted_marker":"LRAT accepted: true","command_identity_sha256":"c"*64,
   "image":MOD.BANK.IMAGE,"job_id":job,"lratreplay_sha256":MOD.BANK.LRATREPLAY_SHA256,"rc":0,
   "schema":"erdos85-small-high-replay-evidence-v1","stderr_sha256":"d"*64,"stdout_sha256":"e"*64}
  ep=bank/f"{job}.replay.json"; ep.write_bytes(MOD.canonical(evidence))
  payload_rows.append({"job_id":job,"path":str(payload),"sha256":psha})
  audits.append({"accepted":True,"accepted_marker":"LRAT accepted: true","cnf_sha256":"a"*64,
   "command_identity_sha256":"c"*64,"image":MOD.BANK.IMAGE,"job_id":job,"ledger_sha256":"b"*64,
   "lratreplay_sha256":MOD.BANK.LRATREPLAY_SHA256,"payload_sha256":psha,"rc":0,
   "replay_evidence":ep.name,"replay_evidence_sha256":MOD.sha(ep),"retained_gzip_sha256":"f"*64,
   "s3_key":f"{MOD.BANK.S3_PREFIX}/{job}.compact-v1.lrat.gz","stderr_sha256":"d"*64,"stdout_sha256":"e"*64})
 payload_doc={"payloads":payload_rows,"root_manifest_sha256":MOD.BANK.ROOT_MANIFEST_SHA256,"schema":MOD.GENERATOR.PAYLOAD_SCHEMA}
 lineage={"root_manifest_sha256":MOD.BANK.ROOT_MANIFEST_SHA256,
  "queue_receipt_sha256":MOD.BANK.QUEUE_RECEIPT_SHA256,"queue_sha256":MOD.BANK.QUEUE_SHA256,
  "worker_receipt_sha256":MOD.BANK.WORKER_RECEIPT_SHA256,"worker_sha256":MOD.BANK.WORKER_SHA256,
  "schema":MOD.LINEAGE_SCHEMA,"work_root":str(root/"work"),"freight_receipt_sha256":MOD.FREIGHT_RECEIPT_SHA256,
  "controller_git_commit":"2"*40,"controller_source":MOD.CONTROLLER_SOURCE,"controller_sha256":"3"*64}
 audit_doc={"jobs":audits,"lineage":lineage,"schema":MOD.BANK.AUDIT_SCHEMA}
 (bank/"payloads.json").write_bytes(MOD.canonical(payload_doc)); (bank/"replay-audit.json").write_bytes(MOD.canonical(audit_doc))
 receipt={"helper_sources":[],"jobs":406,"materializer_sha256":"4"*64,
  "materializer_source":"research/problems/erdos-85-wip-01/sat49/materialize_small_high_payload_bank.py",
  "payload_manifest_sha256":MOD.sha(bank/"payloads.json"),
  "replay_audit_sha256":MOD.sha(bank/"replay-audit.json"),
  "root_manifest":str(root/"root-manifest.json"),"root_manifest_sha256":MOD.BANK.ROOT_MANIFEST_SHA256,
  "schema":MOD.BANK.SCHEMA,"work_root":str(root/"work")}
 (bank/"receipt.json").write_bytes(MOD.canonical(receipt))
 module=root/"Erdos85OrderFortyNineSmallHighCertificates.lean"; module.write_text("-- generated\n")
 module_receipt=root/"module.receipt.json"; module_receipt.write_bytes(MOD.canonical({
  "certificate_dir":str(bank),"generator_sha256":MOD.sha(HERE/"generate_small_high_cube_lean_module.py"),
  "generator_source":MOD.GENERATOR_SOURCE,"include_root":str(bank),"jobs":406,"module":str(module),
  "module_bytes":len(module.read_bytes()),"module_sha256":MOD.sha(module),
  "payload_identity_sha256":MOD.hashlib.sha256(MOD.canonical(payload_rows)).hexdigest(),
  "payload_manifest":str(bank/"payloads.json"),"payload_manifest_sha256":receipt["payload_manifest_sha256"],
  "root_manifest":receipt["root_manifest"],"root_manifest_sha256":MOD.BANK.ROOT_MANIFEST_SHA256,
  "schema":MOD.GENERATOR.MODULE_RECEIPT_SCHEMA,"source_module":MOD.SOURCE_MODULE}))
 return bank,MOD.sha(bank/"receipt.json"),module,module_receipt

class FinalizerTest(unittest.TestCase):
 def test_finalizes_exact_406_and_socket_builder_consumes_v2(self):
  with tempfile.TemporaryDirectory() as directory:
   root=Path(directory); cells={}
   for _,cell,_ in MOD.AGGREGATES.CELLS:
    jobs=[{"id":job} for job in MOD.AGGREGATES.expected_job_ids(cell)]; cells[cell]={"jobs":jobs}
   manifest=root/"manifest.json"; manifest.write_bytes(MOD.canonical({"cells":cells,"schema":"erdos85-small-high-cube-jobs-v1"}))
   old_root=MOD.BANK.ROOT_MANIFEST_SHA256
   try:
    MOD.BANK.ROOT_MANIFEST_SHA256=MOD.sha(manifest)
    bank,pin,module,mreceipt=fixture(root); output=root/"final"
    MOD.build(bank,pin,module,mreceipt,MOD.sha(mreceipt),"a"*40,"1227",output,module.read_bytes())
    self.assertEqual(len(list((output/"leaf-receipts").iterdir())),406)
    pins={"root_manifest_sha256":MOD.sha(manifest),"queue_receipt_sha256":MOD.BANK.QUEUE_RECEIPT_SHA256,
     "queue_sha256":MOD.BANK.QUEUE_SHA256,"worker_receipt_sha256":MOD.BANK.WORKER_RECEIPT_SHA256,
     "worker_sha256":MOD.BANK.WORKER_SHA256}
    SOCKET.APPROVED_PINS=pins.copy()
    artifacts=SOCKET.build(manifest,pins,output/"leaf-receipts",output/"receipt.json",
                           MOD.sha(output/"receipt.json"),"a"*40)
    self.assertEqual(artifacts[3]["socket_count"],406)
   finally:
    MOD.BANK.ROOT_MANIFEST_SHA256=old_root

 def test_module_commit_and_rich_evidence_drift_rejected_without_output(self):
  with tempfile.TemporaryDirectory() as directory:
   root=Path(directory); bank,pin,module,mreceipt=fixture(root); output=root/"final"
   with self.assertRaises(ValueError): MOD.build(bank,pin,module,mreceipt,MOD.sha(mreceipt),"a"*40,"1227",output,b"wrong")
   self.assertFalse(output.exists())
  with tempfile.TemporaryDirectory() as directory:
   root=Path(directory); bank,pin,module,mreceipt=fixture(root); output=root/"final"
   victim=next(bank.glob("*.replay.json")); victim.write_bytes(victim.read_bytes()+b"\n")
   with self.assertRaises(ValueError): MOD.build(bank,pin,module,mreceipt,MOD.sha(mreceipt),"a"*40,"1227",output,module.read_bytes())
   self.assertFalse(output.exists())

 def test_external_module_receipt_pin_is_required(self):
  with tempfile.TemporaryDirectory() as directory:
   root=Path(directory); bank,pin,module,mreceipt=fixture(root); output=root/"final"
   with self.assertRaisesRegex(ValueError,"module receipt SHA mismatch"):
    MOD.build(bank,pin,module,mreceipt,"0"*64,"a"*40,"1227",output,module.read_bytes())
   self.assertFalse(output.exists())

 def test_module_receipt_full_shape_and_canonical_repo_path(self):
  for field,value in (("module", "/wrong/module.lean"),("module_bytes",999),("jobs",405)):
   with self.subTest(field=field),tempfile.TemporaryDirectory() as directory:
    root=Path(directory); bank,pin,module,mreceipt=fixture(root); output=root/"final"
    receipt=json.loads(mreceipt.read_text()); receipt[field]=value; mreceipt.write_bytes(MOD.canonical(receipt))
    with self.assertRaisesRegex(ValueError,"generated module receipt mismatch"):
     MOD.build(bank,pin,module,mreceipt,MOD.sha(mreceipt),"a"*40,"1227",output,module.read_bytes())
    self.assertFalse(output.exists())
  with tempfile.TemporaryDirectory() as directory:
   repo=Path(directory)
   with self.assertRaisesRegex(ValueError,"repository/module commit identity invalid"):
    MOD.committed_bytes(repo,"proofs/Proofs/Generated/Wrong.lean","a"*40)
  with tempfile.TemporaryDirectory() as directory:
   repo=Path(directory); target=repo/MOD.MODULE_REPO_PATH; target.parent.mkdir(parents=True); target.write_bytes(b"reviewed\n")
   for command in (["git","init","-q"],["git","add",MOD.MODULE_REPO_PATH],
                   ["git","-c","user.name=test","-c","user.email=test@example.com","commit","-qm","fixture"]):
    subprocess.run(command,cwd=repo,check=True)
   commit=subprocess.run(["git","rev-parse","HEAD"],cwd=repo,check=True,text=True,
                         stdout=subprocess.PIPE).stdout.strip()
   self.assertEqual(MOD.committed_bytes(repo,MOD.MODULE_REPO_PATH,commit),b"reviewed\n")

if __name__=="__main__":unittest.main()
