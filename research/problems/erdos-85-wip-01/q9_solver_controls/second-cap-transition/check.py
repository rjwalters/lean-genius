from pathlib import Path
import json, hashlib, subprocess, datetime, shutil
p=Path(__file__).resolve().parent
root=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/q9-solver-controls')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
for name in ['ledger.json','campaign-state.json','campaign-plan.json']:
    shutil.copyfile(root/name,p/name)
ledger=json.loads((p/'ledger.json').read_text()); state=json.loads((p/'campaign-state.json').read_text()); plan=json.loads((p/'campaign-plan.json').read_text())
runs={r['id']:r for r in ledger['runs']}; records=[]; source_pins={}
assert state['active_ids']==[7,8] and state['status']=='RUNNING'
assert plan['initial_cap_seconds']==3600 and plan['single_requeue_cap_seconds']==14400
assert plan['aggregate_solver_seconds']==172800 and plan['max_solver_processes']==2
assert plan['proof_logging'] is False and plan['stop_on_first_q9_sat'] is True
for i,m in [(5,10),(6,8),(7,5),(8,4)]:
    r=runs[i]; d=Path(r['directory']); dst=p/('terminal' if i<7 else 'live')/d.name; dst.mkdir(parents=True,exist_ok=True)
    assert (r['n'],r['d'],r['m'],r['seed'])==(80,9,m,0) and r['proof_logging'] is False
    task=next(t for t in plan['q9_order'] if (t['n'],t['m'])==(80,m))
    for key,name,task_key in [('cnf','input.cnf','cnf_sha256'),('metadata','generator-metadata.json','metadata_sha256')]:
        expected=r[key]['sha256']; assert sha(d/name)==sha(Path(r[key]['path']))==expected==task[task_key]
        source_pins[str(d/name)]=expected
    shutil.copyfile(d/'generator-metadata.json',dst/'generator-metadata.json')
    meta=json.loads((d/'generator-metadata.json').read_text())
    assert (meta['n'],meta['minimum_degree'],meta['m'])==(80,9,m) and meta['cnf_sha256']==r['cnf']['sha256']
    for key in ['runner','legacy_helpers','solver']:
        f=Path(r[key]['path']);assert sha(f)==r[key]['sha256'];source_pins[str(f)]=sha(f)
    rec={k:r[k] for k in ['id','n','d','m','status','pid','runner_pid','cap_seconds','retry','started_utc']}
    if i<7:
        assert json.loads((d/'result.json').read_text())==r
        assert sha(d/'solver.log')==r['output']['sha256']
        lines=[x for x in (d/'solver.log').read_text().splitlines() if x.startswith('s ')]
        assert not lines and r['status']=='UNKNOWN' and r['sat_observed'] is False
        assert r['termination_reason']=='wall cap' and r['exit_code']==-15
        assert r['cap_seconds']==14400 and 14400<=r['wall_seconds']<=14405 and r['retry'] is True
        elapsed=(datetime.datetime.fromisoformat(r['ended_utc'])-datetime.datetime.fromisoformat(r['started_utc'])).total_seconds()
        assert abs(elapsed-r['wall_seconds'])<1
        same=[q for q in runs.values() if (q['n'],q['d'],q['m'])==(80,9,m)]
        assert len(same)==2 and sum(q['retry'] for q in same)==1
        prior=runs[i-3];assert prior['status']=='UNKNOWN' and prior['cap_seconds']==3600 and prior['retry'] is False
        for key in ['cnf','metadata']: assert prior[key]['sha256']==r[key]['sha256']
        assert prior['seed']==r['seed']
        for name in ['result.json','solver.log']:shutil.copyfile(d/name,dst/name)
        for pid in [r['pid'],r['runner_pid']]:
            assert subprocess.run(['ps','-p',str(pid),'-o','command='],capture_output=True,text=True).returncode!=0
        rec.update(wall_seconds=r['wall_seconds'],ended_utc=r['ended_utc'],output_sha256=r['output']['sha256'],result_sha256=sha(d/'result.json'),solver_status_lines=lines,retry_exhausted=True)
    else:
        assert r['status']=='RUNNING' and r['retry'] is False and r['cap_seconds']==3600
        cmd=subprocess.check_output(['ps','-p',str(r['pid']),'-o','command='],text=True).strip()
        assert cmd==' '.join(r['command'])
        worker=subprocess.check_output(['ps','-p',str(r['runner_pid']),'-o','command='],text=True).strip()
        assert 'runner_launch.py run' in worker
        predecessor=runs[i-2]
        assert datetime.datetime.fromisoformat(r['started_utc'])>=datetime.datetime.fromisoformat(predecessor['ended_utc'])
        rec.update(live_command=cmd,live_worker_command=worker)
    records.append(rec)
processes=subprocess.check_output(['ps','-axo','pid=,comm='],text=True)
solvers=[line.strip() for line in processes.splitlines() if line.split() and Path(line.split()[-1]).name.lower() in ['kissat','cadical','cryptominisat5','glucose','minisat']]
assert {int(line.split()[0]) for line in solvers}=={runs[7]['pid'],runs[8]['pid']}
controller=subprocess.check_output(['ps','-p',str(state['controller_pid']),'-o','command='],text=True).strip();assert 'campaign.py --run' in controller
now=datetime.datetime.now(datetime.timezone.utc); assert (now-datetime.datetime.fromisoformat(state['updated_utc'])).total_seconds()<10
terminal=sum(r['wall_seconds'] for r in runs.values() if r['status'] not in ['RUNNING','PREPARED'])
assert abs(terminal-state['charged_terminal_seconds'])<1e-6
reserved=sum(runs[i]['cap_seconds']+5 for i in [7,8]);assert terminal+reserved<=172800
accrued=sum((now-datetime.datetime.fromisoformat(runs[i]['started_utc'])).total_seconds() for i in [7,8])
result=dict(status='PASS',utc=now.isoformat(),records=records,live_solver_processes=solvers,controller_command=controller,terminal_solver_seconds=terminal,terminal_solver_hours=terminal/3600,active_wall_accrual_seconds=accrued,active_full_cap_reservation_seconds=reserved,terminal_plus_reserved_seconds=terminal+reserved,aggregate_limit_seconds=172800,scope='Independent terminal record/log/input identity and authorized queue transition check. UNKNOWN provides no existence or nonexistence conclusion. No solver launched or stopped by this checker.')
(p/'processes.txt').write_text(processes)
(p/'source-pins.json').write_text(json.dumps(source_pins,indent=2)+'\n')
(p/'result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
