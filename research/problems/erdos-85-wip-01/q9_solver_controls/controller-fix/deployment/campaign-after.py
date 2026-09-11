#!/usr/bin/env python3
"""Durable authorized queue; shared runner enforces every launch and budget."""
import argparse,fcntl,json,os,subprocess,sys,time
from pathlib import Path
import runner_launch as r
ROOT=Path(__file__).resolve().parent

def key(t):return (t['n'],t['d'],t['m'])
def next_task(plan,ledger):
 if any(x['kind']=='q9' and (x.get('sat_observed') or x['status']=='SAT') for x in ledger['runs']):return None,'SAT_STOP'
 if any(x['kind']=='control' and x.get('model_check',{}).get('status')=='FAIL' for x in ledger['runs']):return None,'ERROR_REQUIRES_INVESTIGATION'
 if any(x['status']=='ERROR' for x in ledger['runs']):return None,'ERROR_REQUIRES_INVESTIGATION'
 if any(x['status'] not in r.ACTIVE|{'SAT','UNSAT','UNKNOWN'} for x in ledger['runs']):return None,'UNRECOGNIZED_STATUS'
 for task in [plan['control']]+plan['q9_order']:
  runs=[x for x in ledger['runs'] if (x['n'],x['d'],x['m'])==key(task)]
  if not runs:return (task,False),'READY'
  if any(x['status'] in r.ACTIVE for x in runs):continue
  last=runs[-1]
  if last['status']=='ERROR':return None,'ERROR_REQUIRES_INVESTIGATION'
  if len(runs)==1 and last['status']=='UNKNOWN':return (task,True),'READY'
  if last['status'] not in {'SAT','UNSAT','UNKNOWN'}:return None,'UNRECOGNIZED_STATUS'
 return None,('WAITING' if any(x['status'] in r.ACTIVE for x in ledger['runs']) else 'ALL_ATTEMPTS_TERMINAL')

def post(body):
 code="import {Squad} from '/Users/rwalters/GitHub/squad/dist/core.js';import {openDb} from '/Users/rwalters/GitHub/squad/dist/db.js';const s=new Squad(openDb(),'codex-sol-2');s.send(process.argv[1]);"
 result=subprocess.run(['node','--input-type=module','-e',code,body],cwd='/Users/rwalters/GitHub/lean-genius',capture_output=True,text=True,timeout=20)
 if result.returncode:raise RuntimeError(result.stderr)
 print(body,flush=True)

def alive(pid):
 try:os.kill(pid,0);return True
 except ProcessLookupError:return False

def run():
 plan=json.loads((ROOT/'campaign-plan.json').read_text());statepath=ROOT/'campaign-state.json';state=json.loads(statepath.read_text()) if statepath.exists() else {'notified_launch':[0,1,2,3],'notified_terminal':[0,1],'pending':[]}
 with (ROOT/'campaign.lock').open('a') as lock:
  fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB);state.update(status='RUNNING',controller_pid=os.getpid(),started_utc=r.legacy.utc());r.legacy.save(statepath,state)
  while True:
   with r.locked() as ledger:r.scan_sat(ledger);snapshot=json.loads(json.dumps(ledger))
   runs=snapshot['runs'];active=[x for x in runs if x['status'] in r.ACTIVE]
   for x in runs:
    if x.get('pid') and x['id'] not in state['notified_launch']:
     post(f"LAUNCH run {x['id']:03d}: N{x['n']} d{x['d']} m{x['m']}, {'4h requeue' if x['retry'] else 'initial'}, seed {x['seed']}, cap {x['cap_seconds']}s, PID {x['pid']}, proof OFF.");state['notified_launch'].append(x['id']);r.legacy.save(statepath,state)
    if x['status'] not in r.ACTIVE and x['id'] not in state['notified_terminal'] and (Path(x['directory'])/'result.json').exists():
     post(f"VERDICT run {x['id']:03d}: N{x['n']} d{x['d']} m{x['m']} {x['status']}, wall {x['wall_seconds']:.3f}s, SAT observed {x.get('sat_observed',False)}, model check {x.get('model_check',{}).get('status','n/a')}; solver report only.");state['notified_terminal'].append(x['id']);r.legacy.save(statepath,state)
   pending=[]
   for job in state['pending']:
    observed=[x for x in runs if (x['n'],x['d'],x['m'])==tuple(job['key'])]
    if len(observed)>job['previous_attempts']:continue
    if not alive(job['pid']):
     state.update(status='LAUNCH_ERROR_REQUIRES_INVESTIGATION',error=job,updated_utc=r.legacy.utc());r.legacy.save(statepath,state);post('CAMPAIGN STOP: launch wrapper ended without a ledger reservation; inspect '+job['log']);return
    pending.append(job)
   state['pending']=pending;task,status=next_task(plan,snapshot);state.update(updated_utc=r.legacy.utc(),queue_status=status,active_ids=[x['id'] for x in active],charged_terminal_seconds=sum(x.get('wall_seconds',0) for x in runs if x['status'] not in r.ACTIVE));r.legacy.save(statepath,state)
   unfinished_output=any(x['id'] not in state['notified_terminal'] for x in runs if x['id']>=2 and x['status'] not in r.ACTIVE)
   if status=='SAT_STOP':
    if not state.get('sat_stop_announced'):post('CAMPAIGN SAT STOP: no further launches; active sibling solvers are stopping. @codex-sol-1 @codex-sol-2 independently decode and verify the saved q9 witness.');state['sat_stop_announced']=True;r.legacy.save(statepath,state)
    if not active and not pending and not unfinished_output:state['status']='SAT_STOP';r.legacy.save(statepath,state);return
   elif status in {'ERROR_REQUIRES_INVESTIGATION','UNRECOGNIZED_STATUS'}:
    state['status']=status;r.legacy.save(statepath,state);post('CAMPAIGN STOP: '+status+'; no automatic retry.');return
   elif status=='ALL_ATTEMPTS_TERMINAL' and not pending and not unfinished_output:
    state['status']=status;r.legacy.save(statepath,state);post('CAMPAIGN COMPLETE: all authorized instance attempts are terminal; prepare the cited verdict from the ledger.');return
   elif task and len(active)+len(pending)<2:
    item,retry=task;jobkey=list(key(item));previous=sum((x['n'],x['d'],x['m'])==key(item) for x in runs)
    if not any(job['key']==jobkey and job['previous_attempts']==previous for job in pending):
     if r.legacy.sha(item['cnf'])!=item['cnf_sha256'] or r.legacy.sha(item['metadata'])!=item['metadata_sha256']:raise RuntimeError('pinned campaign input changed')
     try:
      with r.locked() as ledger:r.policy(ledger,*key(item),item['cnf_sha256'],item['metadata_sha256'],item['seed'],retry)
     except ValueError as exc:
      if '48 aggregate' in str(exc) and not active:
       state.update(status='BUDGET_STOP',reason=str(exc));r.legacy.save(statepath,state);post('CAMPAIGN BUDGET STOP: '+str(exc));return
      if 'slots' not in str(exc) and '48 aggregate' not in str(exc) and 'SAT stop' not in str(exc):raise
     else:
      logfile=ROOT/f"launch-N{item['n']}-m{item['m']}-attempt{previous}.log";command=[sys.executable,'-u',str(ROOT/'runner_launch.py'),'run','--n',str(item['n']),'--d',str(item['d']),'--m',str(item['m']),'--cnf',item['cnf'],'--metadata',item['metadata'],'--seed',str(item['seed'])]+(['--retry'] if retry else [])
      with logfile.open('x') as log:worker=subprocess.Popen(command,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
      state['pending'].append({'key':jobkey,'previous_attempts':previous,'pid':worker.pid,'log':str(logfile),'command':command});r.legacy.save(statepath,state)
   time.sleep(2)
if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('--run',action='store_true');args=parser.parse_args()
 if args.run:run()
 else:
  plan=json.loads((ROOT/'campaign-plan.json').read_text());ledger=json.loads((ROOT/'ledger.json').read_text());print(json.dumps(next_task(plan,ledger)))
