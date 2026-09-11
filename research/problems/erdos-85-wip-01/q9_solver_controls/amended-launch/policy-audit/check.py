from pathlib import Path
import sys,importlib.util,json,copy,hashlib,time
p=Path(__file__).parent;root=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/q9-solver-controls');src=root/'runner_launch.py';sys.path.insert(0,str(root));spec=importlib.util.spec_from_file_location('launch',src);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);ledger=json.loads((root/'ledger.json').read_text());ledger['runs']=[r for r in ledger['runs'] if r['kind']=='control'];cases=[]
def check(name,L,n=80,d=9,order=10,ch='cnf',mh='map',seed=0,retry=False,want=None,error=None):
 try:got=m.policy(copy.deepcopy(L),n,d,order,ch,mh,seed,retry)
 except ValueError as e:
  assert error and error in str(e),(name,str(e));cases.append(dict(name=name,outcome='rejected',reason=str(e)));return
 assert error is None and got==want,(name,got,want);cases.append(dict(name=name,outcome=list(got)))
for n,d,order in m.ORDER:check(f'authorized-{n}-{order}',ledger,n,d,order,want=('q9',3600))
check('authorized-control7',ledger,63,8,7,want=('control',3600))
check('outside-scope',ledger,81,9,1,error='outside amended')
L=copy.deepcopy(ledger);L['controls']={};check('missing-control',L,error='independent N48')
def fake(status,order=10,cap=3600):return dict(id=100,n=80,d=9,m=order,kind='q9',status=status,cap_seconds=cap,wall_seconds=0,cnf={'sha256':'cnf'},metadata={'sha256':'map'},seed=0,sat_observed=False)
L=copy.deepcopy(ledger);L['runs'] +=[fake('PREPARED'),fake('RUNNING',8)];check('both-slots-reserved',L,order=5,error='two solver slots')
L=copy.deepcopy(ledger);L['runs'].append(fake('PREPARED'));check('one-slot-available',L,order=8,want=('q9',3600));check('duplicate-prepared',L,error='already attempted')
L=copy.deepcopy(ledger);L['runs'].append(fake('UNKNOWN'));check('exact-retry',L,retry=True,want=('q9',14400));check('changed-map',L,mh='different',retry=True,error='exact CNF, map and seed');check('changed-cnf',L,ch='different',retry=True,error='exact CNF, map and seed');check('changed-seed',L,seed=1,retry=True,error='exact CNF, map and seed')
L['runs'].append(fake('UNKNOWN'));check('second-retry',L,retry=True,error='one requeue')
L=copy.deepcopy(ledger);L['runs'].append(fake('SAT'));check('terminal-sat',L,order=8,error='first q9 SAT')
L=copy.deepcopy(ledger);r=fake('UNKNOWN');r['sat_observed']=True;L['runs'].append(r);check('observed-sat-even-if-unknown',L,order=8,error='first q9 SAT')
L=copy.deepcopy(ledger);L['runs'][0]['wall_seconds']=m.BUDGET-100-sum(r.get('wall_seconds',0) for r in L['runs'][1:]);check('remaining-budget-truncation',L,want=('q9',95));L['runs'].append(fake('PREPARED',8,90));check('reserved-budget-exhausted',L,error='exhausted or reserved')
x=dict(status='PASS',cases=cases,runner_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),legacy_sha256=hashlib.sha256((root/'runner.py').read_bytes()).hexdigest(),scope='Pure policy on copied ledger only; no live concurrency stress, process lifecycle test, or solver verdict; launch not gated by this audit');(p/'results.json').write_text(json.dumps(x,indent=2)+'\n');print(dict(status=x['status'],cases=len(cases),runner_sha256=x['runner_sha256']))
