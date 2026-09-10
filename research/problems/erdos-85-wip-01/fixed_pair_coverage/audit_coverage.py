from pathlib import Path
import json,hashlib,re,sys
p=Path(__file__).parent;q=p/'coverage_package';m=json.loads((q/'MANIFEST.json').read_text())
allowed={'propext','Classical.choice','Quot.sound'};results=[];missing=[]
for x in m['modules']:
 n=x['name'];source=p/(n+'.lean');copy=q/source.name
 assert hashlib.sha256(source.read_bytes()).hexdigest()==x['sha256'],n
 assert source.read_bytes()==copy.read_bytes(),n
 if n=='LiteralData':
  # Independent no-export data receipt is retained separately; never invent an original receipt.
  receipt=p/'literal_data_independent.json'
  if not receipt.exists():missing.append(n);continue
  r=json.loads(receipt.read_text());assert r['source_sha256']==x['sha256'] and r['returncode']==0 and not r['timeout']
  results.append({'name':n,'exports':0,'evidence':receipt.name,'evidence_sha256':hashlib.sha256(receipt.read_bytes()).hexdigest()});continue
 receipt=p/(n+'.run.json');log=p/(n+'.log')
 if not receipt.exists():missing.append(n);continue
 r=json.loads(receipt.read_text());assert r['returncode']==0 and not r['timeout'],(n,r)
 s=log.read_text();groups=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',s)
 assert all({a.strip() for a in g.split(',') if a.strip()}<=allowed for g in groups),n
 count=len(groups)+len(re.findall('does not depend on any axioms',s));assert count==x['expected_exports'],(n,count)
 assert (p/(n+'.olean')).is_file(),n
 results.append({'name':n,'exports':count,'receipt_sha256':hashlib.sha256(receipt.read_bytes()).hexdigest(),'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest()})
status='complete' if not missing else 'incomplete'
audit={'status':status,'scope':'Coverage certificate only; separate table rejections and final exclusion must compile too.','verified_modules':len(results),'exports':sum(x['exports'] for x in results),'missing':missing,'results':results}
if not missing:assert audit['exports']==m['expected_exports']
(p/'COVERAGE_AUDIT.json').write_text(json.dumps(audit,indent=2)+'\n')
print(json.dumps({k:v for k,v in audit.items() if k!='results'}))
