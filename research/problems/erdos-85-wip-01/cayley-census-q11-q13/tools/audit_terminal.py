from pathlib import Path
import json,hashlib,collections,datetime
p=Path(__file__).resolve().parent;ledger=json.loads((p/'ledger.json').read_text());manifest=json.loads((p/'manifest.json').read_text());need=lambda c,s: None if c else (_ for _ in ()).throw(ValueError(s));sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
need(ledger['status']=='ALL_ATTEMPTS_TERMINAL','campaign still incomplete');need(len(ledger['runs'])==208,'group cover');times=[]
for r,item in zip(ledger['runs'],manifest['groups']):
 need(r['small_group_id']==item['small_group_id'],'group order');d=Path(r['directory']);need(json.loads((d/'result.json').read_text())==r,'result/ledger mismatch');need(sha(d/'solver.log')==r['log_sha256'],'log changed')
 for k,name in [('group','group.json'),('cnf','input.cnf'),('map','map.json')]:need(sha(d/name)==r['input_pins'][k]==item[k+'_sha256'],'input changed')
 lines=[l.strip() for l in (d/'solver.log').read_text().splitlines() if l.startswith('s ')]
 if r['status']=='SAT':need(r['exit_code']==10 and lines==['s SATISFIABLE'] and r['graph_check']['status']=='PASS','bad SAT record')
 elif r['status']=='UNSAT':need(r['exit_code']==20 and lines==['s UNSATISFIABLE'] and not r['sat_observed'],'bad UNSAT record')
 elif r['status']=='UNKNOWN':need(not r['sat_observed'],'UNKNOWN with SAT requires investigation')
 else:raise ValueError('error or active record')
 need(0<r['cap_seconds']<=600 and r['wall_seconds']<=r['cap_seconds']+3,'wall cap')
 need(r['command'][1:5]==['--sat','--strict','--no-color','--seed=0'] and r['command'][5]==f"--time={r['cap_seconds']}" and len(r['command'])==7,'solver settings')
 times.append((r['monotonic_start'],r['monotonic_start']+r['wall_seconds']))
for a,b in zip(times,times[1:]):need(a[1]<=b[0],'overlapping solver intervals')
need(ledger['campaign_wall_seconds']<=86400,'campaign wall')
counts={str(n):dict(collections.Counter(r['status'] for r in ledger['runs'] if r['small_group_id'][0]==n)) for n in [48,80,120,168]}
out={'status':'PASS','scope':'Author terminal artifact/coverage/settings check; not UNSAT certificates','checked_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'runs':208,'counts':counts,'campaign_wall_seconds':ledger['campaign_wall_seconds'],'solver_wall_seconds':sum(r['wall_seconds'] for r in ledger['runs']),'ledger_sha256':sha(p/'ledger.json')};(p/'terminal-audit.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
