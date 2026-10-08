"""Synthetic cloud metadata tests; no actual cloud job, Lean or cache writes."""
import contextlib,copy,io,json,os,shutil,tempfile,unittest
from pathlib import Path
from unittest.mock import patch
import audit_cloud as audit
import test_prepare
from common import sha
class ArtifactChecks(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup)
        self.base=Path(self.tmp.name);self.repo=self.base/'repo';self.root=self.repo/audit.AREA;self.root.mkdir(parents=True)
        self.job=self.base/'job';self.job.mkdir();self.out=self.root/'attempt1';(self.out/'sources/Proofs').mkdir(parents=True)
        f=test_prepare.CoverageChecks();f.setUp();parts=f.ledger();self.manifest=f.manifest
        self.pin='a'*40;self.config={'job':str(self.job),'commit':self.pin,'preflight':False}
        source=b'-- synthetic assembly source\n';self.module='Erdos85H3TripleCompletionCell';self.rel='Proofs/'+self.module+'.lean'
        axioms=sorted({'propext','Classical.choice','Quot.sound'}|{r['native_axiom'] for r in self.manifest['parts']})
        exports={'Erdos85.H3TripleCompletion.'+name:axioms for name in ('threeHighCanonicalRepresentativeExcluded_one','orderFortyNineTripleCellExcluded_three_one')}
        self.plan={'parts':parts,'math_commit':f.manifest['math_commit'],'cell':{'module':'Proofs.'+self.module},
                   'inputs':{'cell_source':{'path':'review.lean','sha256':sha(source)}},'expected_exports':exports,'scope':'synthetic test'}
        self.inputs={'cell_source':source};(self.repo/'review.lean').write_bytes(source)
        self.prior={'results':[]};self.objects={}
        for module in ('Runtime','Engine','Bridge','Split'):
            data=('-- synthetic '+module).encode();p=self.repo/'proofs/Proofs'/(module+'.lean');p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
            self.prior['results'].append({'module':module,'source_sha256':sha(data),'olean_sha256':'b'*64,'olean_bytes':1})
            self.objects[module]={'sha256':'b'*64,'bytes':1,'mtime':1}
        for row in parts:self.objects[row['module'].split('.')[-1]]={'sha256':row['object_sha256'],'bytes':row['object_bytes'],'mtime':1}
        for name in ('prepare.py','common.py','run.py','audit_cloud.py'):(self.root/name).write_text('# synthetic source\n')
        plan_bytes=json.dumps(self.plan).encode();(self.root/'PLAN.json').write_bytes(plan_bytes)
        raw='\n'.join("'"+name+"' depends on axioms: ["+', '.join(axioms)+']' for name in exports).encode()
        (self.out/'compile.log').write_bytes(raw);(self.out/'sources'/self.rel).write_bytes(source)
        obj=b'synthetic cell object';(self.out/(self.module+'.olean')).write_bytes(obj)
        self.objects[self.module]={'sha256':sha(obj),'bytes':len(obj),'mtime':1609459200}
        self.run={'plan_sha256':sha(plan_bytes),'imported_residues':list(range(384)),'cgroup_memory_bytes':16*1024**3,'cgroup_cpu_max':'200000 100000',
                  'started_utc':'2020-01-01T00:00:00+00:00','status':'CELL_COMPILED_PENDING_AUDIT',
                  'step':{'command':['lean','-j1',self.rel,'-o','/workspace/proofs/.lake/build/lib/lean/Proofs/'+self.module+'.olean'],
                          'timeout_seconds':90,'effective_timeout_seconds':90,'launched':True,'log_sha256':sha(raw),'returncode':0,'stop_reason':None},
                  'cell':{'module':'Proofs.'+self.module,'source_sha256':sha(source),'object_sha256':sha(obj),'object_bytes':len(obj),
                          'object_mtime':1609459200,'axiom_exports':[{'theorem':n,'axioms':a} for n,a in exports.items()]}}
        (self.job/'exit').write_text('0');(self.job/'log').write_text('[e85] commit '+self.pin+' (fixture)\n')
        (self.job/'spec').write_text('MEM_GB=16\nTHREADS=1\nCPUS=2\nFULL=1\nTIMEOUT=3m\n')
    def invoke(self,reads=None):
        if self.out.exists():(self.out/'RUN.json').write_text(json.dumps(self.run))
        output=io.StringIO()
        def git(command,**kwargs):return (self.repo/command[-1].split(':',1)[1]).read_bytes()
        with patch.object(audit,'ROOT',self.root),patch.object(audit,'REPO',self.repo),patch.object(audit,'load_inputs',return_value=(self.plan,self.manifest,self.prior,self.inputs)),patch.object(audit,'object_infos',side_effect=reads or [copy.deepcopy(self.objects),copy.deepcopy(self.objects)]),patch.object(audit.subprocess,'check_output',side_effect=git),contextlib.redirect_stdout(output):
            audit.main(self.config)
        return json.loads(output.getvalue())
    def reject(self):
        with self.assertRaises((AssertionError,ValueError)):self.invoke()
    def test_complete_cell_acceptance(self):
        r=self.invoke()['audit'];self.assertEqual(r['status'],'H3_TRIPLE_CELL_ARTIFACT_AUDIT_PASS');self.assertTrue(r['whole_cell_verified'])
        self.assertEqual(len(r['accepted_parts']),384);self.assertEqual(len(r['imported_objects']),388)
    def test_missing_part_object(self):self.objects[self.plan['parts'][5]['module'].split('.')[-1]]=None;self.reject()
    def test_changed_part_object(self):self.objects[self.plan['parts'][5]['module'].split('.')[-1]]['sha256']='c'*64;self.reject()
    def test_missing_cell_object(self):self.objects[self.module]=None;self.reject()
    def test_stale_cell_object(self):
        self.objects[self.module]['mtime']=1;self.run['cell']['object_mtime']=1;self.reject()
    def test_future_cell_object(self):
        self.objects[self.module]['mtime']=9999999999;self.run['cell']['object_mtime']=9999999999;self.reject()
    def test_wrong_cell_object_bytes(self):(self.out/(self.module+'.olean')).write_bytes(b'changed');self.reject()
    def test_wrong_axiom(self):
        path=self.out/'compile.log';raw=path.read_bytes().replace(b'propext',b'sorryAx');path.write_bytes(raw)
        self.run['step']['log_sha256']=sha(raw);self.reject()
    def test_missing_export(self):
        path=self.out/'compile.log';raw=path.read_bytes().split(b'\n')[0];path.write_bytes(raw)
        self.run['step']['log_sha256']=sha(raw);self.reject()
    def test_wrong_execution_pin(self):(self.job/'log').write_text('[e85] commit '+'b'*40+' (fixture)\n');self.reject()
    def test_wrong_command(self):self.run['step']['command'][1]='-j8';self.reject()
    def test_wrong_resource_quota(self):self.run['cgroup_cpu_max']='400000 100000';self.reject()
    def test_changing_object_during_collection(self):
        second=copy.deepcopy(self.objects);second[self.module]['sha256']='c'*64
        with self.assertRaises(AssertionError):self.invoke([self.objects,second])
    def test_failed_compile_gets_no_cell_credit(self):
        (self.job/'exit').write_text('1');self.run['status']='COMPILE_FAILURE';self.run['step']['returncode']=1
        self.objects[self.module]=None;r=self.invoke()['audit']
        self.assertEqual(r['status'],'CELL_ASSEMBLY_NOT_ACCEPTED');self.assertFalse(r['whole_cell_verified'])
    def test_pending_job_has_no_acceptance(self):
        (self.job/'exit').unlink();(self.job/'pid').write_text(str(os.getpid()))
        r=self.invoke();self.assertEqual(r['status'],'PENDING');self.assertNotIn('audit',r)
    def prepare_preflight(self,parts=384):
        shutil.rmtree(self.out);self.objects[self.module]=None;self.config['preflight']=True
        receipt={'status':'READ_ONLY_PREFLIGHT_PASS','plan_sha256':self.run['plan_sha256'],'parts_checked':parts,
                 'prerequisites_checked':4,'cgroup_memory_bytes':16*1024**3,'cgroup_cpu_max':'200000 100000'}
        with (self.job/'log').open('a') as f:f.write(json.dumps(receipt,indent=2)+'\n')
    def test_read_only_preflight(self):
        self.prepare_preflight();r=self.invoke()['audit'];self.assertEqual(r['status'],'CELL_ASSEMBLY_PREFLIGHT_AUDIT_PASS')
        self.assertNotIn('cell',r)
    def test_incomplete_preflight_count_rejected(self):self.prepare_preflight(383);self.reject()
if __name__=='__main__':unittest.main()
