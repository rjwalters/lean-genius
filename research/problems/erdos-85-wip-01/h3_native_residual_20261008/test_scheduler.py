"""Fast cooperative concurrency tests; no Lean and no real cache writes."""
import threading,time,unittest
from scheduler import run_pool
class SchedulerChecks(unittest.TestCase):
    def test_fixed_capacity_exactly_once(self):
        active=0;peak=0;lock=threading.Lock();seen=[];recorded=[]
        def work(r,stop):
            nonlocal active,peak
            with lock:active+=1;peak=max(peak,active);seen.append(r)
            time.sleep(.01)
            with lock:active-=1
            return {'residue':r,'status':'COMPILED_PENDING_AUDIT'}
        result=run_pool(list(range(12)),2,work,recorded.append)
        self.assertLessEqual(peak,2);self.assertEqual(sorted(seen),list(range(12)))
        self.assertEqual(len(recorded),12);self.assertEqual(result['not_started_residues'],[]);self.assertFalse(result['stopped'])
    def test_timeout_stops_peer_and_pending(self):
        barrier=threading.Barrier(2);seen=[];recorded=[]
        def work(r,stop):
            seen.append(r);barrier.wait(timeout=1)
            if r==0:return {'residue':r,'status':'TIMEOUT'}
            self.assertTrue(stop.wait(1));return {'residue':r,'status':'STOP'}
        result=run_pool(list(range(8)),2,work,recorded.append)
        self.assertEqual(sorted(seen),[0,1]);self.assertTrue(result['stopped'])
        self.assertEqual(result['not_started_residues'],list(range(2,8)))
        self.assertEqual({x['status'] for x in recorded},{'TIMEOUT','STOP'})
    def test_exception_is_recorded_and_stops(self):
        recorded=[]
        def work(r,stop):raise RuntimeError('test failure')
        result=run_pool(list(range(8)),2,work,recorded.append)
        self.assertTrue(result['stopped']);self.assertTrue(any(x['status']=='ALARM' for x in recorded))
        self.assertLessEqual(len(result['dispatched_residues']),2)
    def test_preexisting_stop_launches_nothing(self):
        stop=threading.Event();stop.set();seen=[]
        result=run_pool([0,1],2,lambda r,e:seen.append(r),lambda x:None,stop)
        self.assertEqual(seen,[]);self.assertEqual(result['not_started_residues'],[0,1])
    def test_duplicate_rejected(self):
        with self.assertRaises(ValueError):run_pool([1,1],2,lambda r,e:None,lambda x:None)
    def test_unauthorized_worker_count_rejected(self):
        for workers in (1,3,5,8):
            with self.assertRaises(ValueError):run_pool([1],workers,lambda r,e:None,lambda x:None)
    def test_bad_result_is_alarm(self):
        for bad in (None,{}, {'residue':0,'status':'unknown'}, {'residue':8,'status':'COMPILED_PENDING_AUDIT'}):
            recorded=[];result=run_pool([0],2,lambda r,e:bad,recorded.append)
            self.assertTrue(result['stopped']);self.assertEqual(recorded[0]['status'],'ALARM')
    def test_record_failure_signals_stop(self):
        stop=threading.Event()
        def work(r,e):return {'residue':r,'status':'COMPILED_PENDING_AUDIT'}
        def record(result):raise RuntimeError('receipt write failure')
        with self.assertRaises(RuntimeError):run_pool([0,1,2],2,work,record,stop)
        self.assertTrue(stop.is_set())
    def test_recording_is_serialized(self):
        owner=threading.get_ident();threads=[]
        def work(r,e):return {'residue':r,'status':'COMPILED_PENDING_AUDIT'}
        run_pool(list(range(12)),4,work,lambda r:threads.append(threading.get_ident()))
        self.assertEqual(set(threads),{owner})
    def test_invalid_index_rejected(self):
        for r in (-1,384,'89'):
            with self.assertRaises(ValueError):run_pool([r],2,lambda r,e:None,lambda x:None)
if __name__=='__main__':unittest.main()
