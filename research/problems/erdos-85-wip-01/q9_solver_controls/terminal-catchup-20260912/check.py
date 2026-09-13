"""One-time live audit snapshot; not an offline historical replay."""
from pathlib import Path
import json, hashlib, subprocess, datetime, shutil, math
p=Path(__file__).resolve().parent
root=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/q9-solver-controls')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
dt=datetime.datetime.fromisoformat
for name in ['ledger.json','campaign-state.json','campaign-plan.json','runner_launch.py','campaign.py']:
    shutil.copyfile(root/name,p/name)
ledger=json.loads((p/'ledger.json').read_text());state=json.loads((p/'campaign-state.json').read_text());plan=json.loads((p/'campaign-plan.json').read_text())
runs={r['id']:r for r in ledger['runs']}; records=[]; source_pins={}
assert state['active_ids']==[21] and state['status']=='RUNNING'
assert (plan['initial_cap_seconds'],plan['single_requeue_cap_seconds'],plan['aggregate_solver_seconds'],plan['max_solver_processes'])==(3600,14400,172800,2)
assert plan['proof_logging'] is False and plan['stop_on_first_q9_sat'] is True
assert sha(p/'campaign-plan.json')=='888651f8b5e7fa4daaaeecf435a1f014f5332a9ca16c0f73c701cf2de1ffa2b5'
assert sha(p/'campaign.py')=='e67b5b99726594be09a24efc8674384d3d7a45c270f28a0c6506b8453c64a886'
for i in range(9,23):
    r=runs[i];d=Path(r['directory']);live=i==21
    dst=p/('live' if live else 'terminal')/d.name;dst.mkdir(parents=True,exist_ok=True)
    assert r['kind']=='q9' and r['d']==9 and r['seed']==0 and r['proof_logging'] is False
    task=next(t for t in plan['q9_order'] if (t['n'],t['m'])==(r['n'],r['m']))
    for key,name,task_key in [('cnf','input.cnf','cnf_sha256'),('metadata','generator-metadata.json','metadata_sha256')]:
        expected=r[key]['sha256'];assert sha(d/name)==sha(Path(r[key]['path']))==expected==task[task_key],(i,key)
        source_pins[str(d/name)]=expected
    shutil.copyfile(d/'generator-metadata.json',dst/'generator-metadata.json')
    meta=json.loads((d/'generator-metadata.json').read_text())
    assert (meta['n'],meta['minimum_degree'],meta['m'])==(r['n'],9,r['m']) and meta['cnf_sha256']==r['cnf']['sha256']
    for key in ['runner','legacy_helpers','solver']:
        f=Path(r[key]['path']);assert sha(f)==r[key]['sha256'];source_pins[str(f)]=sha(f)
    assert r['command']==[r['solver']['path'],'--sat','--strict','--no-color','--seed=0',f"--time={r['cap_seconds']}",str(d/'input.cnf')]
    lines=[x for x in (d/'solver.log').read_text().splitlines() if x.startswith('s ')]
    assert not lines and r['sat_observed'] is False
    rec={k:r[k] for k in ['id','n','d','m','status','pid','runner_pid','cap_seconds','retry','started_utc']}
    if not live:
        assert json.loads((d/'result.json').read_text())==r
        assert sha(d/'solver.log')==r['output']['sha256']
        assert r['status']=='UNKNOWN' and r['termination_reason']=='wall cap' and r['exit_code']==-15
        expected=6797 if i==22 else 14400 if r['retry'] else 3600
        assert r['cap_seconds']==expected and expected<=r['wall_seconds']<=expected+5
        elapsed=(dt(r['ended_utc'])-dt(r['started_utc'])).total_seconds()
        assert abs(elapsed-r['wall_seconds'])<1,(i,elapsed,r['wall_seconds'])
        for name in ['result.json','solver.log']:shutil.copyfile(d/name,dst/name)
        # A reused PID is not evidence of a historical process still running.
        for pid in [r['pid'],r['runner_pid']]:
            cmd=subprocess.run(['ps','-p',str(pid),'-o','command='],capture_output=True,text=True).stdout
            assert str(d) not in cmd,(i,pid,cmd)
        rec.update(wall_seconds=r['wall_seconds'],ended_utc=r['ended_utc'],output_sha256=r['output']['sha256'],result_sha256=sha(d/'result.json'))
    else:
        assert r['status']=='RUNNING' and r['retry'] is True and r['cap_seconds']==14400 and not (d/'result.json').exists()
        cmd=subprocess.check_output(['ps','-p',str(r['pid']),'-o','command='],text=True).strip();assert cmd==' '.join(r['command'])
        worker=subprocess.check_output(['ps','-p',str(r['runner_pid']),'-o','command='],text=True).strip();assert 'runner_launch.py run' in worker
        rec.update(live_command=cmd,live_worker_command=worker)
    records.append(rec)
# Check exactly one initial and one retry, with identical input and seed, per planned task.
for t in plan['q9_order']:
    pair=sorted([r for r in runs.values() if r['kind']=='q9' and (r['n'],r['d'],r['m'])==(t['n'],9,t['m'])],key=lambda r:r['id'])
    assert len(pair)==2
    a,b=pair;assert a['retry'] is False and b['retry'] is True and a['status']=='UNKNOWN'
    assert a['seed']==b['seed']==0 and a['cap_seconds']==3600
    for key in ['cnf','metadata']:assert a[key]['sha256']==b[key]['sha256']
    assert dt(b['started_utc'])>=dt(a['ended_utc'])
# Reconstruct concurrency and budget at each catch-up launch from persisted timestamps.
allocations=[]
for i in range(9,23):
    r=runs[i];start=dt(r['started_utc'])
    earlier=[q for q in runs.values() if q['id']<i]
    terminal=[q for q in earlier if 'ended_utc' in q and dt(q['ended_utc'])<=start]
    active=[q for q in earlier if q not in terminal]
    assert len(active)<2,(i,[q['id'] for q in active])
    charged=sum(q['wall_seconds'] for q in terminal);reserved=sum(q['cap_seconds']+5 for q in active)
    allowed=math.floor(172800-charged-reserved-5)
    requested=14400 if r['retry'] else 3600
    assert r['cap_seconds']==min(requested,allowed),(i,r['cap_seconds'],allowed)
    allocations.append(dict(id=i,terminal_seconds=charged,active_ids=[q['id'] for q in active],reserved_seconds=reserved,available_cap_seconds=allowed,allocated_cap_seconds=r['cap_seconds']))
processes=subprocess.check_output(['ps','-axo','pid=,comm='],text=True)
solvers=[line.strip() for line in processes.splitlines() if line.split() and Path(line.split()[-1]).name.lower() in ['kissat','cadical','cryptominisat5','glucose','minisat']]
assert {int(line.split()[0]) for line in solvers}=={runs[21]['pid']}
controller=subprocess.check_output(['ps','-p',str(state['controller_pid']),'-o','command='],text=True).strip();assert 'campaign.py --run' in controller
now=datetime.datetime.now(datetime.timezone.utc);assert (now-dt(state['updated_utc'])).total_seconds()<30
terminal=sum(r['wall_seconds'] for r in runs.values() if r['status'] not in ['RUNNING','PREPARED'])
assert abs(terminal-state['charged_terminal_seconds'])<1e-6
reserved=runs[21]['cap_seconds']+5;assert terminal+reserved<=172800
result=dict(status='PASS',utc=now.isoformat(),records=records,launch_allocations=allocations,live_solver_processes=solvers,terminal_solver_seconds=terminal,terminal_solver_hours=terminal/3600,active_full_cap_reservation_seconds=reserved,terminal_plus_reserved_seconds=terminal+reserved,aggregate_limit_seconds=172800,scope='13 terminal artifact audits (009–020,022) and current run021 observation. Historical concurrency and allocation reconstructed from persisted run timestamps, not contemporaneous process observation. UNKNOWN provides no existence or nonexistence conclusion. No solver launched or stopped.')
(p/'processes.txt').write_text(processes)
(p/'source-pins.json').write_text(json.dumps(source_pins,indent=2)+'\n')
(p/'result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['records','launch_allocations']},indent=2))
