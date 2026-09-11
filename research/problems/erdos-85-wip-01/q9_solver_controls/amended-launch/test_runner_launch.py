"""Software fixtures only; never graph controls or q9 experiment results."""
import argparse,json,subprocess,sys,tempfile,time,unittest
from pathlib import Path
from unittest.mock import patch
import runner_launch as r
class Checks(unittest.TestCase):
 def test_policy_scope_gate_reservations(self):
  actual=json.loads((r.ROOT/'ledger.json').read_text());base={'controls':actual['controls'],'runs':[]}
  self.assertEqual(r.scope(80,9,1),'q9');self.assertEqual(r.scope(78,9,1),'q9');self.assertEqual(r.scope(63,8,7),'control')
  self.assertEqual(r.policy(base,80,9,10,'c','m',0,False),('q9',3600))
  with self.assertRaises(ValueError):r.policy({'controls':{},'runs':[]},80,9,10,'c','m',0,False)
  a=dict(id=0,n=63,d=8,m=7,kind='control',status='RUNNING',cap_seconds=3600,wall_seconds=0)
  base['runs']=[a];self.assertEqual(r.policy(base,80,9,10,'c','m',0,False)[1],3600)
  base['runs']=[a,{**a,'id':1,'n':48}]
  with self.assertRaises(ValueError):r.policy(base,80,9,10,'c','m',0,False)
  base['runs']=[a,{**a,'id':1,'status':'UNKNOWN','wall_seconds':r.BUDGET-3610}]
  with self.assertRaises(ValueError):r.policy(base,80,9,10,'c','m',0,False)
 def test_retry_sat(self):
  actual=json.loads((r.ROOT/'ledger.json').read_text());old=dict(id=0,n=80,d=9,m=10,kind='q9',status='UNKNOWN',wall_seconds=3600,cnf={'sha256':'c'},metadata={'sha256':'m'},seed=0)
  ledger={'runs':[old],'controls':actual['controls']};self.assertEqual(r.policy(ledger,80,9,10,'c','m',0,True)[1],14400)
  with self.assertRaises(ValueError):r.policy(ledger,80,9,10,'c','different',0,True)
  old['sat_observed']=True
  with self.assertRaises(ValueError):r.policy(ledger,80,9,8,'c','m',0,False)
 def test_concurrent_atomic_ledger(self):
  with tempfile.TemporaryDirectory() as tmp:
   root=Path(tmp);fake=root/'fake-solver';fake.write_text('#!/usr/bin/env python3\nimport sys,time\nif "--version" in sys.argv: print("fixture")\nelse: time.sleep(0.6); print("s UNKNOWN")\n');fake.chmod(0o755);cnf=root/'fixture.cnf';cnf.write_text('p cnf 1 1\n1 0\n');jobs=[]
   for n,d,m in [(48,7,24),(63,8,7)]:
    meta=root/f'map{n}.json';meta.write_text(json.dumps({'n':n,'minimum_degree':d,'m':m,'cnf_sha256':r.legacy.sha(cnf)}))
    code='import runner_launch as r,sys;from pathlib import Path;r.ROOT=Path(sys.argv[1]);r.KISSAT=Path(sys.argv[2]);sys.argv=["runner_launch","run","--n",sys.argv[3],"--d",sys.argv[4],"--m",sys.argv[5],"--cnf",sys.argv[6],"--metadata",sys.argv[7]];r.main()'
    jobs.append(subprocess.Popen([sys.executable,'-c',code,str(root),str(fake),str(n),str(d),str(m),str(cnf),str(meta)],cwd=r.ROOT,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True))
   for job in jobs:
    out,err=job.communicate(timeout=10);self.assertEqual(job.returncode,0,(out,err))
   ledger=json.loads((root/'ledger.json').read_text());self.assertEqual([x['id'] for x in ledger['runs']],[0,1]);self.assertTrue(all(x['status']=='UNKNOWN' for x in ledger['runs']));self.assertFalse(ledger['controls']);a,b=ledger['runs'];self.assertLess(max(a['monotonic_start'],b['monotonic_start']),min(a['monotonic_start']+a['wall_seconds'],b['monotonic_start']+b['wall_seconds']))
 def test_real_solver_fixture(self):
  with tempfile.TemporaryDirectory() as tmp:
   root=Path(tmp);cnf=root/'fixture.cnf';cnf.write_text('p cnf 2 2\n1 0\n-1 2 0\n');meta=root/'map.json';meta.write_text(json.dumps({'n':48,'minimum_degree':7,'m':24,'cnf_sha256':r.legacy.sha(cnf)}));args=argparse.Namespace(n=48,d=7,m=24,cnf=str(cnf),metadata=str(meta),seed=0,retry=False)
   with patch.object(r,'ROOT',root):r.run(args)
   run=json.loads((root/'ledger.json').read_text())['runs'][0];self.assertEqual(run['status'],'SAT');self.assertEqual(run['model_check']['status'],'PASS');self.assertFalse(run['proof_logging']);self.assertEqual(sum(not x.startswith('-') for x in run['command'][1:]),1)
if __name__=='__main__':unittest.main(verbosity=2)
