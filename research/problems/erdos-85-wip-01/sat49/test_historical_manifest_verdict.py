import copy
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
import historical_verdict_overlay as h


class ManifestJoinedTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup)
        self.directory=Path(self.temp.name)
        self.base=Path(__file__).resolve().parent.parent
        wrapper=self.base/'phase_b_historical_overlay_96/historical-96.json'
        self.data=json.loads(wrapper.read_text())
        self.data['base_overlay']['path']=str((wrapper.parent/self.data['base_overlay']['path']).resolve())
        self.dependencies={name:json.loads((wrapper.parent/ref['path']).read_text()) for name,ref in self.data['extra_sources'].items()}
        self.frozen=(self.base/'phase_b_h1_h3/h1-frozen-candidates.json').read_bytes()

    def load(self):
        for name,value in self.dependencies.items():
            path=self.directory/(name+'.json');raw=json.dumps(value).encode();path.write_bytes(raw)
            self.data['extra_sources'][name]={'path':str(path),'sha256':h.digest(raw)}
        path=self.directory/'wrapper.json';raw=json.dumps(self.data).encode();path.write_bytes(raw)
        return h.load_overlay(path,h.digest(raw),self.frozen)

    def metadata(self, key, transform):
        evidence=self.data['extra_case']['evidence'][0]
        path=evidence[key+'_path'];item=self.dependencies['audit']['metadata'][path]
        item['raw']=transform(item['raw']);item['sha256']=h.digest(item['raw'].encode())
        evidence[key+'_sha256']=item['sha256']
        return item

    def test_valid96_retains95_and_captures_all_sources(self):
        rows,captured=self.load()
        self.assertEqual(len(rows),96);self.assertEqual(len(captured),6)
        old=json.loads(Path(self.data['base_overlay']['path']).read_text())['rows']
        self.assertEqual(rows[:95],old)
        self.assertEqual(rows[-1]['evidence_format'],'manifest_joined_mono')
        self.assertFalse(rows[-1]['proof_replayed'])

    def test_changed95_base_rejected(self):
        self.data['base_overlay']['sha256']='0'*64
        with self.assertRaisesRegex(ValueError,'exact reviewed 95'):self.load()

    def test_unreviewed_extra_case_rejected(self):
        self.data['extra_case']['tag']='other'
        with self.assertRaisesRegex(ValueError,'singleton'):self.load()

    def test_extra_native_failure_rejected(self):
        self.dependencies['comparison']['materialization_receipt']['emit']['returncode']=1
        with self.assertRaisesRegex(ValueError,'native generation/check'):self.load()

    def test_extra_local_table_change_rejected(self):
        self.metadata('local_manifest',lambda text:text.replace('0 0 0 0 0 2','1 0 0 0 0 2',1))
        with self.assertRaisesRegex(ValueError,'local manifest table'):self.load()

    def test_extra_trim_status_change_rejected(self):
        self.metadata('trim_log',lambda text:text.replace('s VERIFIED','s NOT VERIFIED'))
        with self.assertRaisesRegex(ValueError,'not uniquely VERIFIED'):self.load()

    def test_extra_trim_header_change_rejected(self):
        self.metadata('trim_log',lambda text:text.replace('41554 variables','41555 variables'))
        with self.assertRaisesRegex(ValueError,'trim log dimensions'):self.load()

    def test_extra_short_verdict_wrong_status_rejected(self):
        item=self.metadata('verdict',lambda text:text.replace(' UNSAT ',' UNKNOWN '))
        self.data['extra_case']['evidence'][0]['verdict']=item['raw']
        with self.assertRaisesRegex(ValueError,'short verdict framing/status'):self.load()

    def test_extra_cnf_identity_rejected(self):
        self.data['extra_case']['cnf_sha256']='0'*64
        with self.assertRaisesRegex(ValueError,'canonical identity'):self.load()

    def test_extra_proof_replay_claim_rejected(self):
        self.dependencies['audit']['proof_replayed']=True
        with self.assertRaisesRegex(ValueError,'scope mismatch'):self.load()

    def test_extra_duplicate_manifest_row_rejected(self):
        self.metadata('local_manifest',lambda text:text+text.splitlines()[0]+'\n')
        with self.assertRaisesRegex(ValueError,'absent/duplicate'):self.load()


if __name__=='__main__':unittest.main()
