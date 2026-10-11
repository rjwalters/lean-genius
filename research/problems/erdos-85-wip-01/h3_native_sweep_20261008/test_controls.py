"""Metadata and dummy-process tests; no Lean or finite search."""
import copy,json,shutil,sys,tempfile,threading,time,unittest
from pathlib import Path
from common import ROOT,REPO,load_inputs,parse_axioms,part_expectation,cell_expectation
from run import step,classify_failure
class InputTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup)
        self.repo=Path(self.tmp.name);self.root=self.repo/'plan';self.root.mkdir()
        self.plan=json.loads((ROOT/'PLAN.json').read_text())
        for item in self.plan['inputs'].values():
            p=self.repo/item['path'];p.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(REPO/item['path'],p)
        self.save()
    def save(self):(self.root/'PLAN.json').write_text(json.dumps(self.plan))
    def test_valid_inputs(self):self.assertEqual(len(load_inputs(self.root,self.repo)[0]['remaining_residues']),293)
    def test_input_drift(self):
        (self.repo/self.plan['inputs']['manifest']['path']).write_text('{}')
        with self.assertRaises(ValueError):load_inputs(self.root,self.repo)
    def test_missing_residue(self):
        self.plan['remaining_residues'].pop();self.save()
        with self.assertRaises(ValueError):load_inputs(self.root,self.repo)
    def test_duplicate_residue(self):
        self.plan['remaining_residues'].append(1);self.save()
        with self.assertRaises(ValueError):load_inputs(self.root,self.repo)
    def test_wrong_order(self):
        self.plan['remaining_residues'].reverse();self.save()
        with self.assertRaises(ValueError):load_inputs(self.root,self.repo)
    def test_resource_drift(self):
        self.plan['limits']['workers']=2;self.save()
        with self.assertRaises(ValueError):load_inputs(self.root,self.repo)
    def test_unaudited_object_reuse(self):
        self.plan['reused_parts'][0]['object_sha256']='b'*64;self.save()
        with self.assertRaises(ValueError):load_inputs(self.root,self.repo)
class AxiomTests(unittest.TestCase):
    def setUp(self):_,self.manifest,_,_=load_inputs()
    def raw(self,expected):return '\n'.join("'"+n+"' depends on axioms: ["+', '.join(sorted(a))+']' for n,a in expected.items())
    def test_part_exact(self):
        e=part_expectation(self.manifest['parts'][1]);self.assertEqual(len(parse_axioms(self.raw(e),e)),1)
    def test_cell_exact(self):
        e=cell_expectation(self.manifest);self.assertEqual(len(parse_axioms(self.raw(e),e)),2)
    def test_cell_missing_part(self):
        e=cell_expectation(self.manifest);bad=copy.deepcopy(e);next(iter(bad.values())).remove(self.manifest['parts'][20]['native_axiom'])
        with self.assertRaises(ValueError):parse_axioms(self.raw(bad),e)
    def test_cell_unreviewed_extra(self):
        e=cell_expectation(self.manifest);bad=copy.deepcopy(e);next(iter(bad.values())).add('other.axiom')
        with self.assertRaises(ValueError):parse_axioms(self.raw(bad),e)
    def test_duplicate_report(self):
        e=part_expectation(self.manifest['parts'][1]);raw=self.raw(e)
        with self.assertRaises(ValueError):parse_axioms(raw+'\n'+raw,e)
    def test_wrong_residue(self):
        e=part_expectation(self.manifest['parts'][1]);bad=part_expectation(self.manifest['parts'][2])
        with self.assertRaises(ValueError):parse_axioms(self.raw(bad),e)
    def test_sorry(self):
        e=part_expectation(self.manifest['parts'][1])
        with self.assertRaises(ValueError):parse_axioms(self.raw(e)+'\nwarning: sorry',e)
class ProcessTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup);self.root=Path(self.tmp.name)
    def execute(self,code,cap=2,deadline=None):
        return step([sys.executable,'-B','-c',code],self.root/'child.log',cap,time.monotonic()+5 if deadline is None else deadline,self.root/'STOP')
    def test_success(self):
        result=self.execute('print("ok")');self.assertEqual(result['returncode'],0);self.assertIsNone(result['stop_reason'])
    def test_failure(self):self.assertEqual(self.execute('raise SystemExit(7)')['returncode'],7)
    def test_timeout(self):
        r=self.execute('import time;time.sleep(10)',cap=0.1);self.assertEqual(r['stop_reason'],'TIMEOUT');self.assertNotEqual(r['returncode'],0)
    def test_stop_during_child(self):
        timer=threading.Timer(0.1,lambda:(self.root/'STOP').touch());timer.start()
        try:r=self.execute('import time;time.sleep(10)')
        finally:timer.join()
        self.assertEqual(r['stop_reason'],'STOP');self.assertNotEqual(r['returncode'],0)
    def test_stop_before_child(self):
        (self.root/'STOP').touch()
        with self.assertRaises(RuntimeError):self.execute('print("must not run")')
        self.assertFalse((self.root/'child.log').exists())
    def test_global_deadline(self):
        with self.assertRaises(RuntimeError):self.execute('print("must not run")',deadline=time.monotonic()-1)
        self.assertFalse((self.root/'child.log').exists())
    def test_global_cap_shortens_part(self):
        r=self.execute('import time;time.sleep(10)',cap=2,deadline=time.monotonic()+0.1)
        self.assertEqual(r['stop_reason'],'TIMEOUT');self.assertLess(r['effective_timeout_seconds'],0.11)
    def test_existing_log_preserved(self):
        (self.root/'child.log').write_text('historical')
        with self.assertRaises(FileExistsError):self.execute('print("must not run")')
        self.assertEqual((self.root/'child.log').read_text(),'historical')

class SweepPolicyTests(unittest.TestCase):
    def test_full_cap_timeout_is_skipped(self):
        self.assertEqual(classify_failure({'stop_reason':'TIMEOUT','effective_timeout_seconds':90}),'TIMEOUT')
    def test_shortened_timeout_stops_pass(self):
        self.assertEqual(classify_failure({'stop_reason':'TIMEOUT','effective_timeout_seconds':12.0}),'BUDGET_STOP')
    def test_explicit_stop_is_not_skip(self):
        self.assertEqual(classify_failure({'stop_reason':'STOP','effective_timeout_seconds':90}),'STOP')
    def test_compiler_failure_is_not_skip(self):
        self.assertEqual(classify_failure({'stop_reason':None,'effective_timeout_seconds':90}),'COMPILE_FAILURE')

if __name__=='__main__':unittest.main()
