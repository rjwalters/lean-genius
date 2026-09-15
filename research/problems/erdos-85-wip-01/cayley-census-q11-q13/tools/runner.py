#!/usr/bin/env python3
"""Board40: serial, pinned, verdict-only Cayley census; never auto-retry."""
import argparse, datetime, fcntl, hashlib, json, os, signal, subprocess, sys, time
from pathlib import Path
ROOT=Path(__file__).resolve().parent
SOURCE=Path('/Users/rwalters/lean-genius-cayley-sol1-20260913')
SOLVER=Path('/opt/homebrew/bin/kissat').resolve()
REPO=Path('/Users/rwalters/GitHub/lean-genius')

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def utc():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def save(p,x):
 tmp=p.with_suffix(p.suffix+'.tmp')
 with tmp.open('w') as f:json.dump(x,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
 os.replace(tmp,p)
def need(c,s):
 if not c:raise ValueError(s)
def post(body):
 code="import {Squad} from '/Users/rwalters/GitHub/squad/dist/core.js';import {openDb} from '/Users/rwalters/GitHub/squad/dist/db.js';new Squad(openDb(),'codex-sol-3').send(process.argv[1]);"
 r=subprocess.run(['node','--input-type=module','-e',code,body],cwd=REPO,capture_output=True,text=True,timeout=20)
 print(body,flush=True)
 if r.returncode:print('Squad notification failed: '+r.stderr,flush=True)
def statuses(log):return [s.strip() for s in log.read_text().splitlines() if s.startswith('s ')]
def classify(log,code,timedout):
 lines=statuses(log)
 if code==10 and lines==['s SATISFIABLE']:return 'SAT'
 if code==20 and lines==['s UNSATISFIABLE']:return 'UNSAT'
 if timedout and not lines or code==0 and (not lines or lines==['s UNKNOWN']):return 'UNKNOWN'
 return 'ERROR'
def stop(proc):
 if proc.poll() is None:
  os.killpg(proc.pid,signal.SIGTERM)
  try:proc.wait(timeout=2)
  except subprocess.TimeoutExpired:os.killpg(proc.pid,signal.SIGKILL);proc.wait()

def verify_sat(out,item):
 values={}
 for line in (out/'solver.log').read_text().splitlines():
  if line.startswith('v '):
   for x in map(int,line.split()[1:]):
    if x:need(abs(x) not in values or values[abs(x)]==(x>0),'conflicting model');values[abs(x)]=x>0
 count=0;clause=[];header=None
 for line in (out/'input.cnf').read_text().splitlines():
  if not line or line.startswith('c'):continue
  if line.startswith('p '):header=tuple(map(int,line.split()[2:]));continue
  for x in map(int,line.split()):
   if x:clause.append(x)
   else:need(any(values.get(abs(y))==(y>0) for y in clause),'unsatisfied clause');count+=1;clause=[]
 need(header==(item['variables'],item['clauses']) and not clause and count==header[1],'CNF counts')
 need(set(values)==set(range(1,header[0]+1)),'incomplete assignment')
 g=json.loads((out/'group.json').read_text());m=json.loads((out/'map.json').read_text());n,i=item['small_group_id'];t=g['table'];inv=g['inverse']
 need(g['small_group_id']==[n,i] and g['identity']==m['identity']==0,'group identity')
 need(m['selection_variables']=={str(a):a for a in range(1,n)},'selection map')
 S=[a for a in range(1,n) if values[a]];need(len(S)==item['q'] and {inv[a] for a in S}==set(S),'connection size/symmetry')
 adj=[set(t[x][a] for a in S) for x in range(n)]
 for x in range(n):
  need(x not in adj[x] and len(adj[x])==item['q'],'simple regular graph')
  for y in adj[x]:need(x in adj[y],'undirected graph')
 for x in range(n):
  for y in range(x):need(len(adj[x]&adj[y])<=1,'C4 witness invalid')
 graph={'small_group_id':[n,i],'q':item['q'],'connection_set':S,'adjacency':[sorted(a) for a in adj]};save(out/'graph.json',graph)
 check={'status':'PASS','scope':'Author model/graph check; independent second seat required','vertices':n,'degree':item['q'],'edges':sum(map(len,adj))//2,'clauses':count,'graph_sha256':sha(out/'graph.json')};save(out/'graph-check.json',check);return check

def load_manifest():
 m=json.loads((SOURCE/'manifest.json').read_text());expected=[(n,i) for n,c in [(48,52),(80,52),(120,47),(168,57)] for i in range(1,c+1)]
 need([tuple(x['small_group_id']) for x in m['groups']]==expected,'incomplete or reordered group cover')
 for x in m['groups']:
  need(x['q']=={48:7,80:9,120:11,168:13}[x['small_group_id'][0]],'wrong degree')
  for k in ['group','cnf','map']:need(sha(SOURCE/x[k])==x[k+'_sha256'],'input pin changed')
 return m

def run():
 with (ROOT/'campaign.lock').open('a') as lock:
  fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
  path=ROOT/'ledger.json';need(not path.exists(),'existing campaign: inspect it, never automatically restart')
  m=load_manifest();need(not any(Path(s.strip()).name=='kissat' for s in subprocess.check_output(['ps','-axo','comm='],text=True).splitlines()),'another kissat is live')
  save(ROOT/'manifest.json',m);start=time.monotonic();ledger={'authorization':'squad board40','started_utc':utc(),'controller_pid':os.getpid(),'status':'RUNNING','wall_limit_seconds':86400,'monotonic_start':start,'proof_logging':False,'seed':0,'source_manifest_sha256':sha(SOURCE/'manifest.json'),'runner_sha256':sha(__file__),'solver_sha256':sha(SOLVER),'solver_version':subprocess.check_output([str(SOLVER),'--version'],text=True).strip(),'runs':[]};save(path,ledger)
  proc=None
  try:
   for item in m['groups']:
    cap=min(600,int(86400-(time.monotonic()-start)-3))
    if cap<1:ledger['status']='WALL_LIMIT';break
    n,i=item['small_group_id'];out=ROOT/'runs'/f'{n}-{i}';out.mkdir(parents=True,exist_ok=False)
    for key,name in [('group','group.json'),('cnf','input.cnf'),('map','map.json')]:
     raw=(SOURCE/item[key]).read_bytes();need(hashlib.sha256(raw).hexdigest()==item[key+'_sha256'],'changed input');(out/name).write_bytes(raw)
    cmd=[str(SOLVER),'--sat','--strict','--no-color','--seed=0',f'--time={cap}',str(out/'input.cnf')]
    record={'small_group_id':[n,i],'q':item['q'],'structure':item['structure'],'status':'PREPARED','cap_seconds':cap,'input_pins':{k:item[k+'_sha256'] for k in ['group','cnf','map']},'directory':str(out),'command':cmd};ledger['runs'].append(record);save(path,ledger)
    log=out/'solver.log';timedout=False
    with log.open('w') as f:
     t=time.monotonic();proc=subprocess.Popen(cmd,stdout=f,stderr=subprocess.STDOUT,start_new_session=True);record.update(status='RUNNING',pid=proc.pid,started_utc=utc(),monotonic_start=t);save(path,ledger)
     while proc.poll() is None:
      if time.monotonic()-t>=cap:timedout=True;stop(proc);break
      time.sleep(.1)
    record.update(status=classify(log,proc.returncode,timedout),exit_code=proc.returncode,wall_seconds=time.monotonic()-t,ended_utc=utc(),timed_out=timedout,log_sha256=sha(log),sat_observed='s SATISFIABLE' in statuses(log));proc=None
    if record['sat_observed']:
     try:record['graph_check']=verify_sat(out,item)
     except Exception as e:record['graph_check']={'status':'FAIL','error':repr(e)};record['status']='ERROR'
    save(out/'result.json',record);save(path,ledger)
    post(f"CAYLEY {n}-{i}: {record['status']}, {record['wall_seconds']:.3f}s, cap{cap}s, proof OFF. "+('SAT graph saved; @codex-sol-1 @codex-sol-2 independent verification required.' if record['sat_observed'] else 'Solver report only.'))
    if record['sat_observed'] and n in [120,168]:ledger['status']='TARGET_SAT_STOP';break
    if record['status']=='ERROR':ledger['status']='ERROR';break
   else:ledger['status']='ALL_ATTEMPTS_TERMINAL'
  except BaseException as e:
   if proc is not None:stop(proc)
   ledger['status']='ERROR';ledger['error']=repr(e)
   save(path,ledger);raise
  finally:
   ledger['ended_utc']=utc();ledger['campaign_wall_seconds']=time.monotonic()-start;save(path,ledger)
  post('CAYLEY campaign '+ledger['status']+'; controls and independent witness checks determine interpretation. No global nonexistence claim.')

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--run',action='store_true');a=p.parse_args()
 if a.run:run()
 else:print('Use --run once to start board40 census')
