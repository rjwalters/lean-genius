from pathlib import Path
import json,sys,hashlib,subprocess,datetime,copy
p=Path(__file__).parent;root=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/q9-solver-controls');old=json.loads((p/'plan-before.json').read_text());plan=json.loads((root/'campaign-plan.json').read_text());ledger=json.loads((root/'ledger.json').read_text());sys.path.insert(0,str(root));import campaign
expected=[(80,m) for m in [10,8,5,4,2]]+[(78,m) for m in [6,3,2]]+[(80,1),(78,1)];assert [(t['n'],t['m']) for t in plan['q9_order']]==expected
bykey=lambda q:{(t['n'],t['d'],t['m']):t for t in q['q9_order']};assert bykey(plan)==bykey(old);assert plan['control']==old['control']
for k in ['initial_cap_seconds','single_requeue_cap_seconds','aggregate_solver_seconds','max_solver_processes','proof_logging','stop_on_first_q9_sat','input_preflight']:assert plan[k]==old[k],k
hashes={}
for t in [plan['control']]+plan['q9_order']:
 for k in ['cnf','metadata']:
  f=Path(t[k]);h=hashlib.sha256(f.read_bytes()).hexdigest();assert h==t[k+'_sha256'];hashes[str(f)]=h
controls=[copy.deepcopy(r) for r in ledger['runs'] if r['kind']=='control'];tests=0
for completed in range(11):
 synthetic={'runs':controls+[dict(n=t['n'],d=t['d'],m=t['m'],kind='q9',status='UNSAT') for t in plan['q9_order'][:completed]]};selection,status=campaign.next_task(plan,synthetic)
 if completed==10:assert selection is None and status=='ALL_ATTEMPTS_TERMINAL'
 else:assert selection==(plan['q9_order'][completed],False) and status=='READY'
 tests+=1
selection,status=campaign.next_task(plan,copy.deepcopy(ledger));assert selection==(plan['q9_order'][2],False) and status=='READY';tests+=1
live=[]
for r in ledger['runs']:
 if r['status']=='RUNNING':
  cmd=subprocess.check_output(['ps','-p',str(r['pid']),'-o','command='],text=True).strip();assert cmd==' '.join(r['command']);assert r['id'] in [5,6] and r['cap_seconds']==14400;live.append(dict(id=r['id'],pid=r['pid'],started_utc=r['started_utc'],cap_seconds=r['cap_seconds']))
assert {x['id'] for x in live}=={5,6}
receipt=dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),expected_order=expected,unchanged_task_records=True,unchanged_budgets_and_controls=True,verified_input_hashes=hashes,pure_selection_cases=tests,active_requeues=live,source_hashes={str(root/n):hashlib.sha256((root/n).read_bytes()).hexdigest() for n in ['campaign-plan.json','campaign.py']},scope='Read-only plan/input/selection and live-requeue audit; controller reload is separately verified by its deployment receipt.')
(p/'result.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({k:receipt[k] for k in ['status','expected_order','pure_selection_cases','active_requeues']}))
