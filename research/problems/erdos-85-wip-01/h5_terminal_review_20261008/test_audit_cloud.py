"""Exercise terminal acceptance gates using synthetic metadata and temporary files."""
import contextlib,copy,hashlib,io,json,os,tempfile,unittest
from pathlib import Path
from unittest.mock import patch
import audit_cloud as audit
from test_validate_axioms import INV,fixture,log
class ArtifactChecks(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup)
        self.base=Path(self.tmp.name);self.repo=self.base/'repo'
        self.job=self.base/INV['intended_job'];self.job.mkdir()
        self.inv=copy.deepcopy(INV);rows,review=fixture();review['sources']={}
        self.config={'inventory':self.inv,'graph_review':review,'prerequisites':[]}
        self.objects={}
        for module,entry in self.inv['sources'].items():
            path=self.repo/entry['path'];path.parent.mkdir(parents=True,exist_ok=True)
            data=('-- test source '+module+'\n').encode();path.write_bytes(data)
            entry['sha256']=hashlib.sha256(data).hexdigest()
            self.objects[module]={'sha256':'a'*64,'bytes':100,'mtime':1609459200.0}
        self.raw='[e85] job synthetic started 2020-01-01T00:00:00Z\n'
        self.raw+='[e85] commit '+audit.COMMIT+' (test fixture)\n'
        self.raw+='\n'.join('✔ [1/1] Built Proofs.'+m+' (1s)' for m in self.inv['sources'])+'\n'
        self.raw+=log(rows)+'\nBuild completed successfully (44 jobs).\n=== Build succeeded ===\n'
        (self.job/'log').write_text(self.raw);(self.job/'exit').write_text('0\n')
        (self.job/'spec').write_text('\n'.join(('MODE=build','REF=erdos85/h5-formal-20261008','TARGET=Proofs.Erdos85H5Stratum','MEM_GB=48','TIMEOUT=6h','THREADS=8','CPUS=16'))+'\n')
    def run_audit(self,object_reads=None):
        output=io.StringIO()
        def git(command,**kwargs):
            self.assertEqual(command[0],'git')
            return (self.repo/command[-1].split(':',1)[1]).read_bytes()
        with patch.object(audit,'REPO',self.repo),patch.object(audit,'JOB',self.job),patch.object(audit,'object_infos',side_effect=object_reads or [copy.deepcopy(self.objects),copy.deepcopy(self.objects)]),patch.object(audit.subprocess,'check_output',side_effect=git),contextlib.redirect_stdout(output):
            audit.main(self.config)
        return json.loads(output.getvalue())
    def test_complete_fixture_passes(self):
        result=self.run_audit()['audit'];self.assertEqual(result['status'],'H5_STRATUM_ARTIFACT_AUDIT_PASS');self.assertEqual(len(result['results']),44)
    def test_missing_object_rejected(self):
        self.objects[next(iter(self.objects))]=None
        self.assertEqual(self.run_audit()['audit']['status'],'REJECTED')
    def test_stale_object_rejected(self):
        self.objects[next(iter(self.objects))]['mtime']=1
        self.assertEqual(self.run_audit()['audit']['status'],'REJECTED')
    def test_future_object_rejected(self):
        self.objects[next(iter(self.objects))]['mtime']=9999999999
        self.assertEqual(self.run_audit()['audit']['status'],'REJECTED')
    def test_changed_object_rejected(self):
        second=copy.deepcopy(self.objects);second[next(iter(second))]['sha256']='b'*64
        self.assertEqual(self.run_audit([self.objects,second])['audit']['status'],'REJECTED')
    def test_source_hash_drift_rejected(self):
        self.inv['sources'][next(iter(self.inv['sources']))]['sha256']='b'*64
        self.assertEqual(self.run_audit()['audit']['status'],'REJECTED')
    def test_missing_fresh_build_rejected(self):
        module=next(iter(self.objects));(self.job/'log').write_text(self.raw.replace('Built Proofs.'+module+' ','Replayed Proofs.'+module+' '))
        self.assertEqual(self.run_audit()['audit']['status'],'REJECTED')
    def test_terminal_failure_retains_log_without_credit(self):
        (self.job/'exit').write_text('1\n');r=self.run_audit()
        self.assertEqual(r['audit']['status'],'REJECTED');self.assertIn('job.log',r['files'])
    def test_wrong_execution_pin_rejected(self):
        (self.job/'log').write_text(self.raw.replace(audit.COMMIT,'b'*40))
        self.assertEqual(self.run_audit()['audit']['status'],'REJECTED')
    def test_pending_job_writes_no_acceptance(self):
        (self.job/'exit').unlink();(self.job/'pid').write_text(str(os.getpid()))
        r=self.run_audit();self.assertEqual(r['status'],'PENDING');self.assertNotIn('audit',r)
    def test_pending_graph_review_retains_evidence_without_credit(self):
        self.config['graph_review']['status']='AWAITING_EXACT_PRINTED_SET_REVIEW'
        r=self.run_audit();self.assertEqual(r['audit']['status'],'NEEDS_GRAPH_AXIOM_REVIEW');self.assertEqual(len(r['audit']['results']),44)
if __name__=='__main__':unittest.main()
