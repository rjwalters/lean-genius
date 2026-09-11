from pathlib import Path
import os,sys,json,hashlib,signal,subprocess,time,fcntl,sqlite3,datetime,types
p=Path(__file__).parent;root=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/q9-solver-controls');src=root/'campaign.py';sha=lambda b:hashlib.sha256(b).hexdigest()
c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);r=c.execute('select status,resolution,resolved_ts from review_requests where id=2632').fetchone();assert r[0]=='resolved' and r[1].startswith('PASS')
expected=json.loads((p/'source-pins.json').read_text())[str(src)];original=src.read_bytes();assert sha(original)==expected
pins=json.loads((p/'pins.json').read_text());candidate=(p/'campaign-proposed.py').read_bytes();assert sha(candidate)==pins['campaign-proposed.py']
needle="'codex-sol-3');s.send";assert candidate.decode().count(needle)==1;deployed=candidate.decode().replace(needle,"'codex-sol-2');s.send");compile(deployed,str(src),'exec')
state=json.loads((root/'campaign-state.json').read_text());ledger=json.loads((root/'ledger.json').read_text());assert state['controller_pid']==37822 and not state['pending'];assert state['active_ids']==[2,3]
oldpid=state['controller_pid'];cmd=subprocess.check_output(['ps','-p',str(oldpid),'-o','command='],text=True);assert str(src)+' --run' in cmd
active=[x for x in ledger['runs'] if x['status'] in ['RUNNING','PREPARED']];assert len(active)==2 and all(x['status']=='RUNNING' for x in active)
for x in active:os.kill(x['pid'],0);os.kill(x['runner_pid'],0)
stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ');out=p/('deployment-'+stamp);out.mkdir();(out/'campaign-before.py').write_bytes(original);(out/'state-before.json').write_text(json.dumps(state,indent=2)+'\n');(out/'ledger-before.json').write_text(json.dumps(ledger,indent=2)+'\n')
# Stop precisely the controller, not its process group or any solver/worker.
os.kill(oldpid,signal.SIGTERM)
deadline=time.monotonic()+10
while True:
 try:os.kill(oldpid,0)
 except ProcessLookupError:break
 assert time.monotonic()<deadline,'old controller did not exit; no replacement started'
 time.sleep(.1)
with (root/'campaign.lock').open('a') as lock:
 fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
 assert src.read_bytes()==original
 temp=root/'campaign.sol2-replacement.tmp';temp.write_text(deployed);os.chmod(temp,src.stat().st_mode);os.replace(temp,src)
# Import is side-effect-free; exercise accepted guard on a copy before restart.
sys.path.insert(0,str(root));mod=types.ModuleType('offline_deployed');mod.__file__=str(src);exec(compile(deployed,str(src),'exec'),mod.__dict__)
bad=json.loads(json.dumps(ledger));bad['runs'][2]['status']='ERROR';assert mod.next_task(json.loads((root/'campaign-plan.json').read_text()),bad)==(None,'ERROR_REQUIRES_INVESTIGATION')
logpath=root/('campaign-sol2-'+stamp+'.log')
with logpath.open('x') as log:proc=subprocess.Popen([sys.executable,'-u',str(src),'--run'],stdin=subprocess.DEVNULL,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
deadline=time.monotonic()+10
while True:
 assert proc.poll() is None,'new controller exited; inspect '+str(logpath)
 now=json.loads((root/'campaign-state.json').read_text())
 if now.get('controller_pid')==proc.pid and now.get('status')=='RUNNING':break
 assert time.monotonic()<deadline,'new controller failed to register'
 time.sleep(.2)
time.sleep(2.5);assert proc.poll() is None
now=json.loads((root/'campaign-state.json').read_text());after=json.loads((root/'ledger.json').read_text());assert len(after['runs'])==len(ledger['runs']);assert now['active_ids']==[2,3] and not now['pending']
for old,new in zip(ledger['runs'],after['runs']):
 for k in ['id','pid','runner_pid','command','started_utc','monotonic_start','cap_seconds','status']:
  assert old.get(k)==new.get(k),(old['id'],k)
for x in active:os.kill(x['pid'],0);os.kill(x['runner_pid'],0)
for k in ['notified_launch','notified_terminal','pending']:assert state[k]==now[k],k
(out/'campaign-after.py').write_bytes(src.read_bytes());(out/'state-after.json').write_text(json.dumps(now,indent=2)+'\n');(out/'ledger-after.json').write_text(json.dumps(after,indent=2)+'\n')
receipt=dict(status='PASS',review=2632,review_accepted_utc=r[2],old_controller_pid=oldpid,new_controller_pid=proc.pid,old_source_sha256=expected,reviewed_candidate_sha256=sha(candidate),deployed_source_sha256=sha(src.read_bytes()),additional_change='Automation notifier identity codex-sol-3 -> codex-sol-2 for temporary maintenance ownership',unchanged_solver_pids=[x['pid'] for x in active],unchanged_runner_pids=[x['runner_pid'] for x in active],attempts_unchanged=True,caps_and_start_times_unchanged=True,state_notifications_preserved=True,log=str(logpath),utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');(p/'latest-deployment.json').write_text(json.dumps(dict(directory=str(out),receipt=receipt),indent=2)+'\n');print(json.dumps(receipt))
