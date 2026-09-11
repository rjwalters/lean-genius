from pathlib import Path
import json,hashlib,subprocess,datetime
p=Path(__file__).parent;root=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/q9-solver-controls');ledger=json.loads((root/'ledger.json').read_text());plan=json.loads((root/'campaign-plan.json').read_text());sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest();records=[]
for r in ledger['runs'][2:]:
 out=Path(r['directory']);assert sha(out/'input.cnf')==r['cnf']['sha256'];assert sha(out/'generator-metadata.json')==r['metadata']['sha256'];meta=json.loads((out/'generator-metadata.json').read_text());assert (meta['n'],meta['minimum_degree'],meta['m'])==(r['n'],r['d'],r['m']);assert meta['cnf_sha256']==r['cnf']['sha256'];assert r['seed']==0 and r['proof_logging'] is False
 task=next(t for t in [plan['control']]+plan['q9_order'] if (t['n'],t['d'],t['m'])==(r['n'],r['d'],r['m']));assert task['cnf_sha256']==r['cnf']['sha256'] and task['metadata_sha256']==r['metadata']['sha256']
 rec=dict(id=r['id'],n=r['n'],m=r['m'],status=r['status'],pid=r.get('pid'),seed=r['seed'],retry=r['retry'],cap=r['cap_seconds'])
 if r['status'] not in {'RUNNING','PREPARED'}:
  result=json.loads((out/'result.json').read_text());assert result==r;assert sha(out/'solver.log')==r['output']['sha256'];statuses=[s.strip() for s in (out/'solver.log').read_text().splitlines() if s.startswith('s ')]
  if r['status']=='SAT':
   assert r['id']==4 and r['sat_observed'] and r['model_check']['status']=='PASS' and 's SATISFIABLE' in statuses
   control=json.loads((p.parent/'control63-run004-check/independent-receipt.json').read_text());assert control['status']=='PASS' and control['n']==63 and control['edges']==252 and control['c4_count']==0
  else:
   assert r['status']=='UNKNOWN' and not r['sat_observed'];assert r['termination_reason']=='wall cap' and r['exit_code']==-15;assert r['cap_seconds']<=r['wall_seconds']<=r['cap_seconds']+5;assert 's SATISFIABLE' not in statuses and 's UNSATISFIABLE' not in statuses
  rec.update(wall_seconds=r['wall_seconds'],output_sha256=r['output']['sha256'],result_sha256=sha(out/'result.json'),solver_status_lines=statuses)
 else:
  cmd=subprocess.check_output(['ps','-p',str(r['pid']),'-o','command='],text=True).strip();assert cmd==' '.join(r['command']);rec['live_command']=cmd
 if r['retry']:
  prior=[q for q in ledger['runs'] if q['id']<r['id'] and (q['n'],q['d'],q['m'])==(r['n'],r['d'],r['m'])];assert len(prior)==1 and prior[0]['status']=='UNKNOWN';assert r['cap_seconds']==14400
  for k in ['cnf','metadata']:assert r[k]['sha256']==prior[0][k]['sha256']
  assert r['seed']==prior[0]['seed'];rec['retry_identity_verified']=True
 records.append(rec)
processes=subprocess.check_output(['ps','-axo','pid=,comm='],text=True);solvers=[line.strip() for line in processes.splitlines() if line.split() and Path(line.split()[-1]).name.lower() in ['kissat','cadical','cryptominisat5','glucose','minisat']];assert len(solvers)<=2
result=dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),records=records,live_solver_processes=solvers,terminal_solver_seconds=sum(r.get('wall_seconds',0) for r in ledger['runs'] if r['status'] not in {'RUNNING','PREPARED'}),scope='Terminal artifact/status and live launch identity audit; UNKNOWN is not an exclusion. No solver launched by checker.')
(p/'result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
