import concurrent.futures,json,time
import compare as c
start=time.monotonic();c.DEADLINE=start+900
prior=json.loads((c.P/'results-3.json').read_text())['results']
assert len(prior)==3 and all(r['status']=='BYTE_MATCH' for r in prior)
completed={r['tag'] for r in prior};todo=iter([j for j in c.JOBS if j['tag'] not in completed]);results=list(prior);errors=[]
def save():
 record={'target':len(c.JOBS),'completed':len(results),'elapsed_seconds':time.monotonic()-start,'matches':sum(r['status']=='BYTE_MATCH' for r in results),'errors':errors,'results':results,'solver_launched':False,'proof_replay_performed':False}
 temp=c.P/'full-results.tmp';temp.write_text(json.dumps(record,indent=2)+'\n');temp.replace(c.P/'full-results.json')
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
 active={}
 for _ in range(2):
  job=next(todo,None)
  if job:active[pool.submit(c.compare,job)]=job['tag']
 while active:
  done,_=concurrent.futures.wait(active,return_when=concurrent.futures.FIRST_COMPLETED)
  for future in done:
   tag=active.pop(future)
   try:
    r=future.result();results.append(r);print(json.dumps({'completed':len(results),'tag':tag,'status':r['status'],'verified_matches':r['matching_verified_baselines']}),flush=True)
   except BaseException as e:
    errors.append({'tag':tag,'error':repr(e)});c.ABORT.set()
  save()
  if not c.ABORT.is_set():
   while len(active)<2:
    job=next(todo,None)
    if job is None:break
    active[pool.submit(c.compare,job)]=job['tag']
save();print(json.dumps({'completed':len(results),'matches':sum(r['status']=='BYTE_MATCH' for r in results),'errors':errors,'seconds':time.monotonic()-start}),flush=True)
