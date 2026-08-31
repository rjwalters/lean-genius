import gzip, hashlib, importlib.util, json, tempfile, unittest
from pathlib import Path
from unittest import mock

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location("bank", HERE / "materialize_small_high_payload_bank.py")
MOD = importlib.util.module_from_spec(SPEC); assert SPEC.loader is not None; SPEC.loader.exec_module(MOD)


def terminal(job, manifest_sha, cnf, compact, compressed):
    h = lambda value: hashlib.sha256(value).hexdigest()
    fields = {"schema":"erdos85-sat49-terminal-v1","provenance":"fresh","mode":"slow","rc":"20",
        "solve_s":"1","solve_peak_rss_kb":"1","cap_s":"120","generator_kind":"root",
        "generator_sha256":MOD.ROOT_GENERATOR_SHA256,"manifest_sha256":manifest_sha,"emitted_cnf_sha256":h(cnf),
        "solved_cnf_sha256":h(cnf),"cnf_bytes":str(len(cnf)),"maxvar":"1","kissat_sha256":MOD.LEDGER_PINS["kissat_sha256"],
        "raw_lrat_sha256":"b"*64,"raw_lrat_bytes":"1","trim":"VERIFIED","trim_s":"1",
        "trim_peak_rss_kb":"1","drat_trim_sha256":MOD.LEDGER_PINS["drat_trim_sha256"],"compact_lrat_sha256":h(compact),
        "compact_lrat_bytes":str(len(compact)),"compact_s":"1","compact_peak_rss_kb":"1",
        "compactor_sha256":MOD.LEDGER_PINS["compactor_sha256"],"lrat_kind":"compact-v1","native_lratcheck":"VERIFIED",
        "native_lratcheck_s":"1","native_lratcheck_peak_rss_kb":"1","lrat_check_sha256":MOD.LEDGER_PINS["lrat_check_sha256"],
        "lean_lratreplay":"VERIFIED","lean_lratreplay_s":"1","lean_lratreplay_peak_rss_kb":"1",
        "lratreplay_sha256":MOD.LRATREPLAY_SHA256,"lean_image_digest":MOD.LEDGER_PINS["lean_image_digest"],
        "compact_lrat_gz_sha256":h(compressed),"compact_lrat_gz_bytes":str(len(compressed)),
        "upload":"uploaded","remote_sha256":h(compressed)}
    return f"2026-08-31T00:00:00Z {job} UNSAT " + " ".join(f"{k}={v}" for k,v in fields.items()) + "\n"


def fixture(root):
    cells={}
    for _,cell,_ in MOD.AGGREGATES.CELLS:
        cells[cell]={"jobs":[{"id":j} for j in MOD.AGGREGATES.expected_job_ids(cell)]}
    manifest=root/"manifest.json"; manifest.write_bytes(MOD.canonical({"cells":cells,"schema":"erdos85-small-high-cube-jobs-v1"}))
    MOD.ROOT_MANIFEST_SHA256=MOD.sha(manifest)
    work=root/"work"; work.mkdir()
    lin={"root_manifest_sha256":MOD.ROOT_MANIFEST_SHA256,"queue_receipt_sha256":MOD.QUEUE_RECEIPT_SHA256,
        "queue_sha256":MOD.QUEUE_SHA256,"worker_receipt_sha256":MOD.WORKER_RECEIPT_SHA256,
        "worker_sha256":MOD.WORKER_SHA256}
    (work/"lineage.json").write_bytes(MOD.canonical(lin))
    cnf=b"p cnf 1 1\n1 0\n"; compact=b"2 0 1 0\n"
    gz_path=root/"sample.gz"
    with gz_path.open("wb") as raw_stream:
        with gzip.GzipFile(filename="",mode="wb",mtime=0,fileobj=raw_stream) as stream: stream.write(compact)
    compressed=gz_path.read_bytes()
    for job in MOD.jobs(json.loads(manifest.read_text())):
        directory=work/job; directory.mkdir()
        (directory/"ledger.line").write_text(terminal(job,MOD.ROOT_MANIFEST_SHA256,cnf,compact,compressed))
    def materialize(job,path): path.write_bytes(cnf)
    def fetch(job,path): path.write_bytes(compressed)
    def replay(job,cnf_path,payload): return {"accepted":True,"accepted_marker":"LRAT accepted: true",
        "command_identity_sha256":"c"*64,"image":MOD.IMAGE,"lratreplay_sha256":MOD.LRATREPLAY_SHA256,
        "rc":0,"stdout_sha256":"d"*64,"stderr_sha256":"e"*64}
    return manifest,work,materialize,fetch,replay


class PayloadBankTest(unittest.TestCase):
    def test_exact_406_bank_and_receipt_last(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory); manifest,work,materialize,fetch,replay=fixture(root)
            output=root/"bank"; MOD.build(manifest,work,output,materialize,fetch,replay)
            payload=json.loads((output/"payloads.json").read_text())
            audit=json.loads((output/"replay-audit.json").read_text())
            self.assertEqual(len(payload["payloads"]),406); self.assertEqual(len(audit["jobs"]),406)
            self.assertTrue(all((output/f"{row['job_id']}.lrat").is_file() for row in payload["payloads"]))
            self.assertEqual((output/"receipt.json").read_bytes(),MOD.canonical(json.loads((output/"receipt.json").read_text())))

    def test_missing_ledger_and_failed_replay_publish_nothing(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory); manifest,work,materialize,fetch,replay=fixture(root)
            next(work.glob("*/ledger.line")).unlink(); output=root/"bank"
            with self.assertRaises(ValueError): MOD.build(manifest,work,output,materialize,fetch,replay)
            self.assertFalse(output.exists())
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory); manifest,work,materialize,fetch,replay=fixture(root)
            output=root/"bank"
            def failed(*args): return {"accepted":False,"accepted_marker":"LRAT accepted: true",
                "command_identity_sha256":"c"*64,"image":MOD.IMAGE,"lratreplay_sha256":MOD.LRATREPLAY_SHA256,
                "rc":1,"stdout_sha256":"d"*64,"stderr_sha256":"e"*64}
            with self.assertRaises(ValueError): MOD.build(manifest,work,output,materialize,fetch,failed)
            self.assertFalse(output.exists())

    def test_gzip_or_lineage_drift_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory); manifest,work,materialize,fetch,replay=fixture(root)
            def bad_fetch(job,path): path.write_bytes(b"bad")
            with self.assertRaises(Exception): MOD.build(manifest,work,root/"bank",materialize,bad_fetch,replay)
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory); manifest,work,materialize,fetch,replay=fixture(root)
            value=json.loads((work/"lineage.json").read_text()); value["worker_sha256"]="0"*64
            (work/"lineage.json").write_bytes(MOD.canonical(value))
            with self.assertRaises(ValueError): MOD.build(manifest,work,root/"bank",materialize,fetch,replay)

    def test_swapped_ledger_and_symlinked_job_directory_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory); manifest,work,materialize,fetch,replay=fixture(root)
            ledgers=list(work.glob("*/ledger.line")); ledgers[1].write_bytes(ledgers[0].read_bytes())
            with self.assertRaisesRegex(ValueError,"terminal or approved"):
                MOD.build(manifest,work,root/"bank",materialize,fetch,replay)
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory); manifest,work,materialize,fetch,replay=fixture(root)
            victim=next(path for path in work.iterdir() if path.is_dir()); moved=root/"moved"; victim.rename(moved); victim.symlink_to(moved)
            with self.assertRaisesRegex(ValueError,"symlinked"):
                MOD.build(manifest,work,root/"bank",materialize,fetch,replay)

    def test_publication_time_ledger_mutation_leaves_no_receipt(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory); manifest,work,materialize,fetch,replay=fixture(root); output=root/"bank"
            victim=next(work.glob("*/ledger.line")); original=MOD.shutil.copyfileobj; changed=False
            def mutate(source,target,*args,**kwargs):
                nonlocal changed
                result=original(source,target,*args,**kwargs)
                if not changed and Path(target.name).parent==output:
                    changed=True; victim.write_bytes(victim.read_bytes()+b"\n")
                return result
            with mock.patch.object(MOD.shutil,"copyfileobj",mutate), self.assertRaises(ValueError):
                MOD.build(manifest,work,output,materialize,fetch,replay)
            self.assertTrue(output.exists()); self.assertFalse((output/"receipt.json").exists())


if __name__=="__main__": unittest.main()
