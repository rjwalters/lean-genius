from pathlib import Path
import json,sys,types,hashlib,copy,time
p=Path(__file__).parent;src=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/q9-solver-controls/campaign.py');sys.path.insert(0,str(src.parent));original=src.read_text();plan=json.loads((src.parent/'campaign-plan.json').read_text());tasks=[plan['control']]+plan['q9_order'];live=json.loads((src.parent/'ledger.json').read_text());history=[x for x in live['runs'] if x['id']<2]
anchor=" if any(x['kind']=='control' and x.get('model_check',{}).get('status')=='FAIL' for x in ledger['runs']):return None,'ERROR_REQUIRES_INVESTIGATION'"
replacement=anchor+"\n if any(x['status']=='ERROR' for x in ledger['runs']):return None,'ERROR_REQUIRES_INVESTIGATION'\n if any(x['status'] not in r.ACTIVE|{'SAT','UNSAT','UNKNOWN'} for x in ledger['runs']):return None,'UNRECOGNIZED_STATUS'"
assert original.count(anchor)==1;patched=original.replace(anchor,replacement);(p/'campaign-proposed.py').write_text(patched)
def module(code):
 m=types.ModuleType('offline_campaign');m.__file__=str(src);exec(compile(code,str(src),'exec'),m.__dict__);return m
before=module(original);after=module(patched)
def run(task,status):return dict(n=task['n'],d=task['d'],m=task['m'],status=status,kind='control' if task['n']==63 else 'q9',sat_observed=False)
def norm(answer):
 task,status=answer
 return (None if task is None else ([task[0][k] for k in ['n','d','m']],task[1]),status)
def expected(i,retry=False):return (([tasks[i][k] for k in ['n','d','m']],retry),'READY')
cases=[]
def add(label,runs,want):cases.append((label,{'runs':copy.deepcopy(history+runs)},want))
add('empty_queue',[],expected(0))
# Every prefix of terminal successes must advance to the next task.
for i in range(12):
 runs=[run(t,'SAT' if j==0 else 'UNSAT') for j,t in enumerate(tasks[:i])]
 add('terminal_prefix_'+str(i),runs,expected(i) if i<11 else (None,'ALL_ATTEMPTS_TERMINAL'))
for i,t in enumerate(tasks):
 prefix=[run(q,'SAT' if j==0 else 'UNSAT') for j,q in enumerate(tasks[:i])]
 add('retry_'+str(i),prefix+[run(t,'UNKNOWN')],expected(i,True))
 add('exhausted_retry_'+str(i),prefix+[run(t,'UNKNOWN'),run(t,'UNKNOWN')],expected(i+1) if i<10 else (None,'ALL_ATTEMPTS_TERMINAL'))
 # Errors in any later queue position must stop even when the first task is absent.
 add('error_priority_'+str(i),[run(t,'ERROR')],(None,'ERROR_REQUIRES_INVESTIGATION'))
 add('invalid_status_priority_'+str(i),[run(t,'CORRUPT')],(None,'UNRECOGNIZED_STATUS'))
 if i:
  add('sat_priority_'+str(i),[run(t,'SAT')],(None,'SAT_STOP'))
  observed=run(t,'RUNNING');observed['sat_observed']=True
  add('observed_sat_priority_'+str(i),[observed],(None,'SAT_STOP'))
add('all_active',[run(t,'RUNNING') for t in tasks],(None,'WAITING'))
add('existing_q9_active_control_next',[run(tasks[1],'RUNNING'),run(tasks[2],'RUNNING')],expected(0))
add('control_active_q9_next',[run(tasks[0],'RUNNING')],expected(1))
badcontrol=run(tasks[0],'SAT');badcontrol['model_check']={'status':'FAIL'}
add('bad_control_global',[badcontrol],(None,'ERROR_REQUIRES_INVESTIGATION'))
failures=[]
for label,ledger,want in cases:
 got=norm(before.next_task(plan,ledger))
 if got!=want:failures.append(dict(case=label,expected=want,actual=got))
 assert norm(after.next_task(plan,ledger))==want,label
result=dict(status='ORIGINAL_FAIL_PROPOSED_PASS',cases=len(cases),original_failures=failures,proposed_failures=0,audit_did_not_write_live_ledger=True,scope='Offline pure next_task audit and proposed source copy only; no live edit/restart/process/lifecycle audit.')
(p/'result.json').write_text(json.dumps(result,indent=2)+'\n');(p/'source-pins.json').write_text(json.dumps({str(src):hashlib.sha256(original.encode()).hexdigest(),str(src.parent/'campaign-plan.json'):hashlib.sha256((src.parent/'campaign-plan.json').read_bytes()).hexdigest()},indent=2)+'\n');print(json.dumps(dict(cases=len(cases),original_failures=len(failures),proposed_failures=0)))
