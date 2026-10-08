"""Synthetic artifact metadata tests; these never establish mathematical credit."""
import copy,json,unittest
from datetime import datetime,timezone
from common import sha,part_expectation
import test_prepare
from validate_run import verify_run,AREA,INIT

class ReceiptChecks(unittest.TestCase):
    def setUp(self):
        fixture=test_prepare.PlanChecks();fixture.setUp();self.plan=fixture.plan();self.manifest=copy.deepcopy(fixture.manifest)
        self.files={'PLAN.json':json.dumps(self.plan).encode(),'shared.log':b''};self.objects={}
        self.start=1791464400
        self.run={'started_utc':self.ts(0),'plan_sha256':sha(self.files['PLAN.json']),'workers':2,
                  'cgroup_memory_bytes':32*1024**3,'cgroup_cpu_max':'400000 100000','initializer':INIT,
                  'reused_residues':[r['residue'] for r in self.plan['reused_parts']],
                  'status':'RESIDUAL_COMPLETED_PENDING_AUDIT','steps':[],'parts':[],'attempts':[],
                  'library':{'sha256':'0'*64,'bytes':1},'dispatched_residues':[89,100,200],'not_started_residues':[]}
        library='/workspace/'+AREA+'/attempt1/libH3TripleRuntime.so'
        shared=self.step('shared',0,1,60,['leanc','-O3','-DLEAN_EXPORTING','-shared','-fPIC',
            '/workspace/proofs/.lake/build/ir/Proofs/Erdos85H3TripleCompletionRuntime.c','-o',library],b'')
        self.run['steps'].append(shared)
        for i,r in enumerate(self.plan['residual_residues']):
            row=self.manifest['parts'][r];source=('synthetic source '+str(r)).encode();row['source_sha256']=sha(source)
            self.files['sources/'+row['source_path']]=source
            axioms=sorted(part_expectation(row)[row['theorem']]);raw=("'"+row['theorem']+"' depends on axioms: ["+', '.join(axioms)+']').encode()
            name=f'part{r:03d}';self.files[name+'.log']=raw
            step=self.step(name,2+i*2,3+i*2,1800,['lean','-j1','--plugin='+library+'='+INIT,row['source_path'],'-o',
                '/workspace/proofs/.lake/build/lib/lean/Proofs/'+row['module'].split('.')[-1]+'.olean'],raw)
            item={'residue':r,'status':'COMPILED_PENDING_AUDIT','module':row['module'],'source_sha256':row['source_sha256'],
                  'object_sha256':'0'*64,'object_bytes':1,'object_mtime':self.start+3+i*2,
                  'axiom_exports':[{'theorem':row['theorem'],'axioms':axioms}]}
            self.run['steps'].append(step);self.run['parts'].append(item);self.run['attempts'].append({**item,'step':step})
            self.objects[r]={'sha256':item['object_sha256'],'bytes':1,'mtime':item['object_mtime']}
    def ts(self,offset):return datetime.fromtimestamp(self.start+offset,timezone.utc).isoformat()
    def step(self,name,begin,end,cap,command,raw):
        return {'name':name,'command':command,'launched':True,'returncode':0,'stop_reason':None,
                'timeout_seconds':cap,'effective_timeout_seconds':cap,'elapsed_seconds':end-begin,
                'started_utc':self.ts(begin),'finished_utc':self.ts(end),'log_sha256':sha(raw)}
    def check(self,rc=0):return verify_run(self.run,self.plan,self.manifest,self.files,self.objects,self.start+2000,rc)
    def reject(self):
        with self.assertRaises((AssertionError,ValueError,KeyError)):self.check()
    def test_complete_receipt(self):
        r=self.check();self.assertEqual(r['status'],'H3_RESIDUAL_ARTIFACT_AUDIT_PASS');self.assertFalse(r['whole_cell_verified'])
    def test_wrong_resource_quota(self):self.run['cgroup_cpu_max']='800000 100000';self.reject()
    def test_wrong_memory(self):self.run['cgroup_memory_bytes']=64*1024**3;self.reject()
    def test_wrong_worker_count(self):self.run['workers']=4;self.reject()
    def test_changed_plan(self):self.files['PLAN.json']+=b' ';self.reject()
    def test_changed_source(self):self.files['sources/'+self.manifest['parts'][89]['source_path']]=b'drift';self.reject()
    def test_changed_raw_log(self):self.files['part089.log']+=b'changed';self.reject()
    def test_wrong_axioms(self):
        raw=self.files['part089.log'].replace(b'propext',b'sorryAx');self.files['part089.log']=raw
        self.run['steps'][1]['log_sha256']=sha(raw);self.reject()
    def test_wrong_object_hash(self):self.objects[89]['sha256']='1'*64;self.reject()
    def test_stale_object(self):
        self.objects[89]['mtime']=self.start-1
        self.run['parts'][0]['object_mtime']=self.start-1;self.run['attempts'][0]['object_mtime']=self.start-1;self.reject()
    def test_future_object(self):
        self.objects[89]['mtime']=self.start+3000
        self.run['parts'][0]['object_mtime']=self.start+3000;self.run['attempts'][0]['object_mtime']=self.start+3000;self.reject()
    def test_wrong_command(self):self.run['steps'][1]['command'][1]='-j8';self.reject()
    def test_missing_part(self):self.run['parts'].pop();self.reject()
    def test_duplicate_attempt(self):self.run['attempts'].append(self.run['attempts'][0]);self.reject()
    def test_out_of_order_dispatch(self):self.run['dispatched_residues'].reverse();self.reject()
    def test_failed_shared_library(self):self.run['steps'][0]['returncode']=1;self.reject()
    def test_failed_part(self):self.run['steps'][1]['returncode']=1;self.reject()
    def test_excess_concurrency(self):
        for s in self.run['steps'][1:]:s['started_utc']=self.ts(2);s['finished_utc']=self.ts(5)
        self.reject()
    def test_partial_timeout_has_no_whole_credit(self):
        self.run['parts'].pop();item=self.run['attempts'][-1];s=item['step']
        item['status']='TIMEOUT';s.update(stop_reason='TIMEOUT',returncode=-9,elapsed_seconds=1800,finished_utc=self.ts(1806))
        self.objects[200]=None;self.run['status']='TIMEOUT'
        result=self.check(rc=1);self.assertEqual(result['status'],'PARTIAL_RESIDUAL_ARTIFACT_AUDIT')
        self.assertEqual(result['unresolved_residues'],[200]);self.assertFalse(result['whole_cell_verified'])
    def test_partial_timeout_object_cannot_remain_in_cache(self):
        self.run['parts'].pop();item=self.run['attempts'][-1];s=item['step']
        item['status']='TIMEOUT';s.update(stop_reason='TIMEOUT',returncode=-9,elapsed_seconds=1800,finished_utc=self.ts(1806))
        self.run['status']='TIMEOUT'
        with self.assertRaises(AssertionError):self.check(rc=1)
if __name__=='__main__':unittest.main()
