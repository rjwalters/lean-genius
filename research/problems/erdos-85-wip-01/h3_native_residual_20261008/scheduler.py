"""Bounded fail-fast worker pool with no retries and cooperative child cancellation."""
from concurrent.futures import ThreadPoolExecutor,wait,FIRST_COMPLETED
import threading

def run_pool(tasks,workers,work,record,stop_event=None):
    if workers not in (2,4):raise ValueError('Only the authorized fixed worker counts are supported')
    if any(not isinstance(r,int) or not 0<=r<384 for r in tasks):raise ValueError('Invalid residual index')
    if len(set(tasks))!=len(tasks):raise ValueError('Duplicate task would be an unauthorized retry')
    stop=stop_event if stop_event is not None else threading.Event()
    pending=iter(tasks);active={};started=[];results=[]
    def wrapped(task):
        if stop.is_set():return {'residue':task,'status':'NOT_STARTED'}
        try:
            result=work(task,stop)
            if not isinstance(result,dict) or result.get('residue')!=task:
                raise ValueError('Worker returned wrong residue or result type')
            if result.get('status') not in ('COMPILED_PENDING_AUDIT','TIMEOUT','STOP','BUDGET_STOP','ALARM','COMPILE_FAILURE','NOT_STARTED'):
                raise ValueError('Worker returned invalid status')
        except Exception as exc:result={'residue':task,'status':'ALARM','exception':repr(exc)}
        if result['status']!='COMPILED_PENDING_AUDIT':stop.set()
        return result
    with ThreadPoolExecutor(max_workers=workers) as pool:
        def fill():
            while len(active)<workers and not stop.is_set():
                try:task=next(pending)
                except StopIteration:return
                future=pool.submit(wrapped,task);active[future]=task;started.append(task)
        fill()
        while active:
            done,_=wait(active,return_when=FIRST_COMPLETED)
            for future in sorted(done,key=lambda f:active[f]):
                result=future.result();del active[future]
                # Recording is serialized in the coordinator; workers never race on RUN.json.
                try:record(result)
                except Exception:
                    stop.set();raise
                results.append(result)
            fill()
    return {'dispatched_residues':started,'results':results,
            'not_started_residues':[r for r in tasks if r not in started or any(x['residue']==r and x['status']=='NOT_STARTED' for x in results)],
            'stopped':stop.is_set()}
