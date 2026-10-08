"""Metadata and tiny-file transfer tests; no Lean or real cache mutations."""
import copy,hashlib,tempfile,unittest
from pathlib import Path
from transfer_pair import inspect,publish,validate_triple,JOB
class TransferChecks(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup)
        base=Path(self.tmp.name);self.source=base/'source';self.dest=base/'dest';self.source.mkdir();self.dest.mkdir()
        self.rows=[]
        for i in range(3):
            module='TestPart'+str(i);data=('verified '+str(i)).encode();(self.source/(module+'.olean')).write_bytes(data)
            self.rows.append({'module':module,'source_sha256':'test','object':{'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data)}})
    def test_inspection_does_not_write(self):
        self.assertEqual(len(inspect(self.rows,self.source,self.dest)),3);self.assertEqual(list(self.dest.iterdir()),[])
    def test_atomic_copy_and_idempotence(self):
        r=publish(self.rows,self.source,self.dest);self.assertEqual(len(r['created']),3)
        self.assertEqual(publish(self.rows,self.source,self.dest)['created'],[])
        self.assertEqual(sorted(p.name for p in self.dest.iterdir()),[r['module']+'.olean' for r in self.rows])
    def test_conflict_leaves_all_files_untouched(self):
        last=self.dest/'TestPart2.olean';last.write_bytes(b'other')
        with self.assertRaises(ValueError):publish(self.rows,self.source,self.dest)
        self.assertEqual(list(self.dest.iterdir()),[last]);self.assertEqual(last.read_bytes(),b'other')
    def test_corrupt_source_stops_before_copy(self):
        (self.source/'TestPart2.olean').write_bytes(b'bad')
        with self.assertRaises(ValueError):publish(self.rows,self.source,self.dest)
        self.assertEqual(list(self.dest.iterdir()),[])
    def test_same_size_wrong_hash_rejected(self):
        data=(self.source/'TestPart1.olean').read_bytes();(self.source/'TestPart1.olean').write_bytes(b'x'*len(data))
        with self.assertRaises(ValueError):inspect(self.rows,self.source,self.dest)
    def test_wrong_size_rejected(self):
        self.rows[0]['object']['bytes']+=1
        with self.assertRaises(ValueError):inspect(self.rows,self.source,self.dest)
class TripleGateChecks(unittest.TestCase):
    def setUp(self):
        self.spec={'triple_source_commit':'test-pin'}
        self.audit={'status':'H3_TRIPLE_CELL_ARTIFACT_AUDIT_PASS','authoritative_exit':0,'job':JOB.name,
                    'execution_commit':'test-pin','reused_residues':[0,3,4,5,162],
                    'accepted_new_residues':[r for r in range(384) if r not in [0,3,4,5,162]],
                    'cell':{'module':'Proofs.Erdos85H3TripleCompletionCell'}}
    def test_full_gate(self):validate_triple(self.audit,self.spec)
    def test_partial_rejected(self):
        self.audit['status']='PARTIAL_CAMPAIGN_ARTIFACT_AUDIT'
        with self.assertRaises(ValueError):validate_triple(self.audit,self.spec)
    def test_failed_exit_rejected(self):
        self.audit['authoritative_exit']=1
        with self.assertRaises(ValueError):validate_triple(self.audit,self.spec)
    def test_wrong_job_rejected(self):
        self.audit['job']='other'
        with self.assertRaises(ValueError):validate_triple(self.audit,self.spec)
    def test_wrong_commit_rejected(self):
        self.audit['execution_commit']='other'
        with self.assertRaises(ValueError):validate_triple(self.audit,self.spec)
    def test_missing_residue_rejected(self):
        self.audit['accepted_new_residues'].pop()
        with self.assertRaises(ValueError):validate_triple(self.audit,self.spec)
    def test_duplicate_residue_rejected(self):
        self.audit['accepted_new_residues'][0]=0
        with self.assertRaises(ValueError):validate_triple(self.audit,self.spec)
    def test_wrong_cell_rejected(self):
        self.audit['cell']['module']='Other'
        with self.assertRaises(ValueError):validate_triple(self.audit,self.spec)
if __name__=='__main__':unittest.main()
