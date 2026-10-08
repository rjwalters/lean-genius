"""Metadata and tiny-file transfer tests; no Lean or real cache mutations."""
import copy,hashlib,json,tempfile,unittest
from pathlib import Path
from transfer_pair import inspect,publish,validate_triple,load_spec,sha
from fixture_cell import complete_cell_fixture
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
class BindingChecks(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup)
        self.root=Path(self.tmp.name);self.raw=b'{"historical": true}\n'
        (self.root/'SOURCE.json').write_bytes(self.raw)
        self.binding={'status':'CELL_ACCEPTANCE_BOUND','source_spec_sha256':sha(self.raw),
            'job':'20261008T235959-erdos85__h3-triple-formal-20261007-999999',
            'execution_commit':'b'*40,'triple_audit_sha256':'c'*64,
            'triple_audit_path':'research/test/AUDIT.json'}
    def save(self):
        (self.root/'INTEGRATION.json').write_text(json.dumps(self.binding))
    def test_bound_source_loads_unchanged(self):
        self.save();self.assertEqual(load_spec(self.root)['triple_producer'],self.binding)
        self.assertEqual((self.root/'SOURCE.json').read_bytes(),self.raw)
    def test_missing_binding_rejected(self):
        with self.assertRaises(FileNotFoundError):load_spec(self.root)
    def test_changed_source_rejected(self):
        self.save();(self.root/'SOURCE.json').write_bytes(self.raw+b' ')
        with self.assertRaises(ValueError):load_spec(self.root)
    def test_wrong_producer_or_hash_rejected(self):
        for field in ('status','job','execution_commit','triple_audit_sha256'):
            with self.subTest(field=field):
                original=self.binding[field];self.binding[field]='invalid';self.save()
                with self.assertRaises(ValueError):load_spec(self.root)
                self.binding[field]=original
    def test_nonlocal_audit_path_rejected(self):
        for path in ('/tmp/AUDIT.json','../AUDIT.json','research/else.json'):
            with self.subTest(path=path):
                self.binding['triple_audit_path']=path;self.save()
                with self.assertRaises(ValueError):load_spec(self.root)
class TripleGateChecks(unittest.TestCase):
    def setUp(self):
        self.spec,self.audit=complete_cell_fixture()
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
        self.audit['accepted_parts'].pop()
        with self.assertRaises(ValueError):validate_triple(self.audit,self.spec)
    def test_duplicate_residue_rejected(self):
        self.audit['accepted_parts'][1]=self.audit['accepted_parts'][0]
        with self.assertRaises(ValueError):validate_triple(self.audit,self.spec)
    def test_wrong_cell_rejected(self):
        self.audit['cell']['module']='Other'
        with self.assertRaises(ValueError):validate_triple(self.audit,self.spec)
    def test_unbound_historical_source_spec_rejected(self):
        self.spec.pop('triple_producer')
        with self.assertRaises(ValueError):validate_triple(self.audit,self.spec)
    def test_wrong_cell_axioms_rejected(self):
        self.audit['cell']['axiom_exports'][0]['axioms'].pop()
        with self.assertRaises(ValueError):validate_triple(self.audit,self.spec)
    def test_wrong_part_axioms_rejected(self):
        self.audit['accepted_parts'][0]['axioms'][0]='sorryAx'
        with self.assertRaises(ValueError):validate_triple(self.audit,self.spec)
    def test_wrong_part_source_rejected(self):
        self.audit['accepted_parts'][0]['source_sha256']='wrong'
        with self.assertRaises(ValueError):validate_triple(self.audit,self.spec)
    def test_unverified_whole_cell_rejected(self):
        self.audit['whole_cell_verified']=False
        with self.assertRaises(ValueError):validate_triple(self.audit,self.spec)
if __name__=='__main__':unittest.main()
