#!/usr/bin/env python3
"""Editor50462/50463: two host solver slots, N48 launch gate, durable shared ledger."""
import argparse,contextlib,fcntl,json,math,os,signal,subprocess,time,shutil
from pathlib import Path
import runner as legacy
ROOT=Path(__file__).resolve().parent
KISSAT=legacy.KISSAT
BUDGET=48*3600
ACTIVE={'PREPARED','RUNNING'}
ORDER=[(80,9,m) for m in (10,8,5,4,2,1)]+[(78,9,m) for m in (6,3,2,1)]
AUTH={'source':'squad messages 50462 and 50463','launch_gate':'independently verified N48 control','concurrency':2,'proof_logging':False}

@contextlib.contextmanager
def locked():
 with (ROOT/'runner.lock').open('a') as lock:
  fcntl.flock(lock,fcntl.LOCK_EX)
  path=ROOT/'ledger.json';ledger=json.loads(path.read_text()) if path.exists() else {'runs':[],'controls':{}}
  yield ledger
  legacy.save(path,ledger)

def scope(n,d,m):
 if (n,d,m) in [(48,7,24),(63,8,7),(63,8,1)]:return 'control'
 if (n,d,m) in ORDER:return 'q9'
 raise ValueError('outside amended launch scope')

def scan_sat(ledger):
 for r in ledger['runs']:
  if r['kind']=='q9' and not r.get('sat_observed') and r.get('directory'):
   if legacy.observed_sat(Path(r['directory'])/'solver.log'):r['sat_observed']=True
 return [r['id'] for r in ledger['runs'] if r['kind']=='q9' and (r.get('sat_observed') or r['status']=='SAT')]

def policy(ledger,n,d,m,cnf_hash,metadata_hash,seed,retry):
 kind=scope(n,d,m);runs=ledger['runs']
 if scan_sat(ledger):raise ValueError('first q9 SAT stop: independently verify the saved witness')
 active=[r for r in runs if r['status'] in ACTIVE]
 if len(active)>=2:raise ValueError('two solver slots occupied; inspect existing handles')
 previous=[r for r in runs if (r['n'],r['d'],r['m'])==(n,d,m)]
 if retry:
  if len(previous)!=1 or previous[0]['status']!='UNKNOWN':raise ValueError('one requeue only after terminal UNKNOWN')
  old=previous[0]
  if (old['cnf']['sha256'],old['metadata']['sha256'],old['seed'])!=(cnf_hash,metadata_hash,seed):raise ValueError('retry must preserve exact CNF, map and seed')
 elif previous:raise ValueError('instance already attempted')
 if kind=='q9':
  receipt=ledger['controls'].get('48')
  if not receipt:raise ValueError('independent N48 positive control required')
  legacy.verify_pin(receipt['receipt'])
  for artifact in receipt['artifacts']:legacy.verify_pin(artifact)
 spent=sum(r.get('wall_seconds',0) for r in runs if r['status'] not in ACTIVE)
 reserved=sum(r['cap_seconds']+5 for r in active)
 cap=min(14400 if retry else 3600,math.floor(BUDGET-spent-reserved-5))
 if cap<1:raise ValueError('48 aggregate solver-hours exhausted or reserved')
 return kind,cap

def live_solvers():
 rows=subprocess.check_output(['ps','-axo','pid=,comm='],text=True).splitlines();answer=[]
 for row in rows:
  parts=row.strip().split(None,1)
  if len(parts)==2 and Path(parts[1]).name.lower() in {'kissat','cadical','cryptominisat5','glucose','minisat'}:answer.append(int(parts[0]))
 return answer

def update(idx,**fields):
 with locked() as ledger:
  r=ledger['runs'][idx]
  if 'sat_observed' in fields:fields['sat_observed']=bool(fields['sat_observed'] or r.get('sat_observed'))
  r.update(fields)
  return dict(r)

def run(args):
 cnf=legacy.pin(args.cnf);metadata=legacy.pin(args.metadata)
 if not cnf['path'].endswith('.cnf'):raise ValueError('plain CNF required')
 meta=json.loads(Path(metadata['path']).read_text())
 if (meta.get('n'),meta.get('minimum_degree'),meta.get('m'))!=(args.n,args.d,args.m):raise ValueError('generator metadata scope mismatch')
 if meta.get('cnf_sha256')!=cnf['sha256']:raise ValueError('metadata does not bind exact CNF')
 with locked() as ledger:
  kind,cap=policy(ledger,args.n,args.d,args.m,cnf['sha256'],metadata['sha256'],args.seed,args.retry)
  if len(live_solvers())+sum(r['status']=='PREPARED' for r in ledger['runs'])>=2:raise ValueError('two host solver processes already live/reserved')
  idx=len(ledger['runs']);out=ROOT/'runs'/f'{idx:03d}-N{args.n}-m{args.m}';out.mkdir(parents=True,exist_ok=False)
  shutil.copyfile(cnf['path'],out/'input.cnf');shutil.copyfile(metadata['path'],out/'generator-metadata.json')
  if legacy.sha(out/'input.cnf')!=cnf['sha256'] or legacy.sha(out/'generator-metadata.json')!=metadata['sha256']:raise ValueError('input changed during snapshot')
  command=[str(KISSAT),'--sat','--strict','--no-color',f'--seed={args.seed}',f'--time={cap}',str(out/'input.cnf')]
  r=dict(id=idx,n=args.n,d=args.d,m=args.m,kind=kind,seed=args.seed,retry=args.retry,cap_seconds=cap,cnf=cnf,metadata=metadata,solver=legacy.pin(KISSAT),runner=legacy.pin(__file__),legacy_helpers=legacy.pin(legacy.__file__),command=command,solver_version=subprocess.check_output([str(KISSAT),'--version'],text=True).strip(),proof_logging=False,status='PREPARED',sat_observed=False,wall_seconds=0,prepared_utc=legacy.utc(),directory=str(out),runner_pid=os.getpid(),authorization=AUTH)
  ledger['runs'].append(r);ledger['launch_authorization']=AUTH
 process=None;started=time.monotonic();reason=None;fields={"status":"ERROR","error":"interrupted before solver monitor"}
 def stop(signum,frame):raise KeyboardInterrupt(f'signal {signum}')
 signal.signal(signal.SIGTERM,stop);signal.signal(signal.SIGINT,stop)
 try:
  with (out/'solver.log').open('w') as log:
   with locked() as ledger:
    if scan_sat(ledger):raise RuntimeError('SAT stop reached before Popen')
    if len(live_solvers())>=2:raise RuntimeError('host slots changed before Popen')
    process=subprocess.Popen(command,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
    ledger['runs'][idx].update(status='RUNNING',pid=process.pid,pgid=process.pid,started_utc=legacy.utc(),monotonic_start=started)
   print(json.dumps({'event':'LAUNCH','id':idx,'n':args.n,'m':args.m,'pid':process.pid,'cap_seconds':cap,'directory':str(out)}),flush=True)
   try:
    while process.poll() is None:
     elapsed=time.monotonic()-started
     if elapsed>=cap:reason='wall cap';break
     with locked() as ledger:
      if any(j!=idx for j in scan_sat(ledger)):reason='first q9 SAT observed in another run';break
     try:process.wait(timeout=min(1,max(.001,cap-elapsed)))
     except subprocess.TimeoutExpired:pass
   except KeyboardInterrupt as exc:reason=str(exc)
   finally:
    if process.poll() is None:
     os.killpg(process.pid,signal.SIGTERM)
     try:process.wait(timeout=2)
     except subprocess.TimeoutExpired:os.killpg(process.pid,signal.SIGKILL);process.wait()
  fields={'exit_code':process.returncode,'status':'UNKNOWN' if reason else legacy.parse_output(out/'solver.log',process.returncode)}
  if reason:fields['termination_reason']=reason
 except (Exception,KeyboardInterrupt) as exc:
  fields={'status':'ERROR','error':repr(exc)}
  if process is not None and process.poll() is None:os.killpg(process.pid,signal.SIGKILL);process.wait()
 finally:
  fields.update(wall_seconds=time.monotonic()-started,ended_utc=legacy.utc(),sat_observed=legacy.observed_sat(out/'solver.log'))
  r=update(idx,**fields)
 if (out/'solver.log').exists():r=update(idx,output=legacy.pin(out/'solver.log'))
 if r.get('sat_observed'):
  try:model=legacy.check_model(out/'input.cnf',out/'solver.log')
  except Exception as exc:model={'status':'FAIL','error':repr(exc)}
  r=update(idx,model_check=model)
 legacy.save(out/'result.json',r)
 print(json.dumps({'event':'VERDICT','id':idx,'n':args.n,'m':args.m,'status':r['status'],'wall_seconds':r['wall_seconds'],'sat_observed':r['sat_observed']}),flush=True)

def main():
 parser=argparse.ArgumentParser(description=__doc__);sub=parser.add_subparsers(dest='action',required=True);p=sub.add_parser('run')
 for name in ['n','d','m']:p.add_argument('--'+name,type=int,required=True)
 for name in ['cnf','metadata']:p.add_argument('--'+name,required=True)
 p.add_argument('--seed',type=int,default=0);p.add_argument('--retry',action='store_true');sub.add_parser('status');p=sub.add_parser('register-control');p.add_argument('receipt');args=parser.parse_args()
 if args.action=='run':
  if args.seed<0:raise ValueError('seed must be nonnegative')
  run(args)
 else:
  with locked() as ledger:
   if args.action=='register-control':legacy.register(args,ledger,ROOT/'ledger.json')
   else:scan_sat(ledger);print(json.dumps(ledger,indent=2))
if __name__=='__main__':main()
