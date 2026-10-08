"""Dummy subprocess tests only: no Lean, finite search, or production cache."""
import hashlib,sys,tempfile,threading,time,unittest
from pathlib import Path
from process import run_child
from scheduler import run_pool

class ProcessTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup)
        self.root=Path(self.tmp.name);self.stop=threading.Event()
    def run_code(self,code,cap=2,deadline=None,name='child',stop=None):
        return run_child([sys.executable,'-B','-c',code],self.root/(name+'.log'),cap,
                         time.monotonic()+5 if deadline is None else deadline,self.root/'STOP',stop or self.stop)
    def test_success_and_log_hash(self):
        r=self.run_code('print("ok")');self.assertEqual(r['returncode'],0);self.assertIsNone(r['stop_reason'])
        self.assertEqual(r['log_sha256'],hashlib.sha256(b'ok\n').hexdigest());self.assertFalse(self.stop.is_set())
    def test_failure_sets_shared_stop(self):
        r=self.run_code('raise SystemExit(7)');self.assertEqual(r['returncode'],7);self.assertTrue(self.stop.is_set())
    def test_full_cap_timeout(self):
        r=self.run_code('import time;time.sleep(5)',cap=.1)
        self.assertEqual(r['stop_reason'],'TIMEOUT');self.assertEqual(r['effective_timeout_seconds'],.1)
        self.assertTrue(self.stop.is_set());self.assertNotEqual(r['returncode'],0)
    def test_short_global_budget_is_distinct(self):
        r=self.run_code('import time;time.sleep(5)',deadline=time.monotonic()+.1)
        self.assertEqual(r['stop_reason'],'BUDGET_STOP');self.assertLess(r['effective_timeout_seconds'],2)
    def test_expired_budget_does_not_launch(self):
        r=self.run_code('raise Exception("must not run")',deadline=time.monotonic()-1)
        self.assertFalse(r['launched']);self.assertEqual(r['stop_reason'],'BUDGET_STOP')
        self.assertFalse((self.root/'child.log').exists())
    def test_preexisting_stop_does_not_launch(self):
        self.stop.set();r=self.run_code('raise Exception("must not run")')
        self.assertFalse(r['launched']);self.assertEqual(r['stop_reason'],'STOP')
        self.assertFalse((self.root/'child.log').exists())
    def test_file_stop_terminates_child(self):
        timer=threading.Timer(.1,lambda:(self.root/'STOP').touch());timer.start()
        try:r=self.run_code('import time;time.sleep(5)')
        finally:timer.join()
        self.assertEqual(r['stop_reason'],'STOP');self.assertNotEqual(r['returncode'],0)
    def test_existing_log_is_immutable(self):
        (self.root/'child.log').write_text('original')
        with self.assertRaises(FileExistsError):self.run_code('print("must not run")')
        self.assertEqual((self.root/'child.log').read_text(),'original');self.assertTrue(self.stop.is_set())
    def test_launch_failure_stops_pool(self):
        with self.assertRaises(FileNotFoundError):
            run_child(['/nonexistent/residual-test'],self.root/'child.log',2,time.monotonic()+5,self.root/'STOP',self.stop)
        self.assertTrue(self.stop.is_set())
    def test_timeout_cancels_live_peer_and_prevents_next(self):
        barrier=threading.Barrier(2);seen=[];recorded=[]
        def work(r,stop):
            seen.append(r);barrier.wait(timeout=2)
            item=self.run_code('import time;time.sleep(5)',cap=.2 if r==0 else 3,name=str(r),stop=stop)
            return {'residue':r,'status':item['stop_reason'] or 'COMPILED_PENDING_AUDIT','step':item}
        before=time.monotonic();pool=run_pool([0,1,2,3],2,work,recorded.append,self.stop)
        self.assertLess(time.monotonic()-before,2);self.assertEqual(sorted(seen),[0,1])
        self.assertEqual({r['status'] for r in recorded},{'TIMEOUT','STOP'})
        self.assertEqual(pool['not_started_residues'],[2,3]);self.assertTrue(pool['stopped'])
    def test_process_group_kills_descendant(self):
        # A surviving grandchild would create this marker after its parent times out.
        marker=self.root/'descendant-survived'
        descendant='import time;from pathlib import Path;time.sleep(.5);Path('+repr(str(marker))+').touch()'
        code='import subprocess,sys,time;subprocess.Popen([sys.executable,"-B","-c",'+repr(descendant)+']);print("spawned",flush=True);time.sleep(5)'
        r=self.run_code(code,cap=.2);self.assertEqual(r['stop_reason'],'TIMEOUT')
        self.assertIn('spawned',(self.root/'child.log').read_text());time.sleep(.5)
        self.assertFalse(marker.exists())
if __name__=='__main__':unittest.main()
