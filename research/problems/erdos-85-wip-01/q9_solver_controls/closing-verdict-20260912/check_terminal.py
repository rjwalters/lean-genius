from pathlib import Path
import json,hashlib,subprocess,datetime,shutil
p=Path(__file__).resolve().parent;root=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/q9-solver-controls');sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
for n in ['ledger.json','campaign-state.json','campaign-plan.json']:shutil.copyfile(root/n,p/n)
l=json.loads((p/'ledger.json').read_text());s=json.loads((p/'campaign-state.json').read_text());plan=json.loads((p/'campaign-plan.json').read_text());runs=l['runs'];r=next(q for q in runs if q['id']==21);d=Path(r['directory']);out=p/'terminal-021';out.mkdir(exist_ok=True)
assert len(runs)==23 and {q['id'] for q in runs}==set(range(23))
assert s['status']=='ALL_ATTEMPTS_TERMINAL' and s['active_ids']==[]
assert all(q['status'] not in ['RUNNING','PREPARED'] for q in runs)
assert json.loads((d/'result.json').read_text())==r and sha(d/'solver.log')==r['output']['sha256']
assert (r['status'],r['termination_reason'],r['exit_code'],r['sat_observed'])==('UNKNOWN','wall cap',-15,False)
assert r['cap_seconds']==14400 and 14400<=r['wall_seconds']<=14405 and r['retry'] is True
assert not [line for line in (d/'solver.log').read_text().splitlines() if line.startswith('s ')]
t=next(t for t in plan['q9_order'] if (t['n'],t['m'])==(80,1))
for key,name,tk in [('cnf','input.cnf','cnf_sha256'),('metadata','generator-metadata.json','metadata_sha256')]:assert sha(d/name)==sha(Path(r[key]['path']))==r[key]['sha256']==t[tk]
for key in ['runner','legacy_helpers','solver']:assert sha(Path(r[key]['path']))==r[key]['sha256']
for n in ['result.json','solver.log','generator-metadata.json']:shutil.copyfile(d/n,out/n)
q9=[q for q in runs if q['kind']=='q9'];assert len(q9)==20 and all(q['status']=='UNKNOWN' and q['sat_observed'] is False for q in q9)
for task in plan['q9_order']:
 pair=sorted([q for q in q9 if (q['n'],q['m'])==(task['n'],task['m'])],key=lambda q:q['id']);assert len(pair)==2
 a,b=pair;assert a['retry'] is False and b['retry'] is True and a['cap_seconds']==3600
 assert b['cap_seconds']==(6797 if b['id']==22 else 14400)
 for k in ['cnf','metadata']:assert a[k]['sha256']==b[k]['sha256']
 assert a['seed']==b['seed']==0
 assert datetime.datetime.fromisoformat(b['started_utc'])>=datetime.datetime.fromisoformat(a['ended_utc'])
wall=sum(q['wall_seconds'] for q in runs);assert abs(wall-s['charged_terminal_seconds'])<1e-6 and wall<=172800
ps=subprocess.check_output(['ps','-axo','pid=,comm='],text=True);solvers=[x for x in ps.splitlines() if x.split() and Path(x.split()[-1]).name.lower() in ['kissat','cadical','cryptominisat5','glucose','minisat']];assert not solvers
for pid in [r['pid'],r['runner_pid'],s['controller_pid']]:assert subprocess.run(['ps','-p',str(pid),'-o','command='],capture_output=True).returncode!=0
(p/'processes.txt').write_text(ps)
result=dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),terminal_run=21,log_sha256=sha(out/'solver.log'),result_sha256=sha(out/'result.json'),all_runs=23,q9_attempts=20,q9_statuses=['UNKNOWN'],terminal_solver_seconds=wall,terminal_solver_hours=wall/3600,remaining_seconds=172800-wall,solver_processes=[],scope='Final run021 raw artifact/input check, full ledger terminal accounting and ten initial/retry pairs. Earlier raw terminal audits remain separate. No nonexistence conclusion.')
(p/'terminal-check.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
